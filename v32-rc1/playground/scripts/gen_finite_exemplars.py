#!/usr/bin/env python3
"""Author the per-node finite-exemplar Lean snippets for the hierarchy page.

Each entry maps a hierarchy node (a Mathlib class) to a *self-contained* Lean
snippet: `import Mathlib`, a fresh finite carrier, its operation(s), an
`instance` declared at exactly that node's class (laws proved by `decide`), and
a short usage example that touches only that class's API.  Because the carrier
is an instance of *nothing higher* in the hierarchy, the examples cannot mention
a higher class.  Output: site/finite_exemplars.json  ({node: {disp, code}}).

Every snippet here is compile-checked by scripts/check_finite_exemplars.sh.
"""
import json, os

# node -> (display carrier, snippet).  Order = the four ladders of FiniteExemplars.lean.
E = {}

E["Mul"] = ("Mag2", r"""import Mathlib
/-- A bare magma: a set with `*` and no laws (material nonimplication `a ∧ ¬b`). -/
inductive Mag2 | ff | tt
  deriving DecidableEq, Fintype, Repr
open Mag2
def mag2mul : Mag2 → Mag2 → Mag2
  | tt, ff => tt
  | _,  _  => ff
instance : Mul Mag2 := ⟨mag2mul⟩

-- `Mul` gives you `*` and nothing else — not even commutativity:
#eval tt * ff
example : tt * ff ≠ ff * tt := by decide
""")

E["CommMagma"] = ("RPS", r"""import Mathlib
/-- Rock–Paper–Scissors: `a * b` is the winner. Commutative, but NOT associative. -/
inductive RPS | rock | paper | scissors
  deriving DecidableEq, Fintype, Repr
open RPS
def rpsMul : RPS → RPS → RPS
  | rock, scissors => rock     | scissors, rock => rock
  | paper, rock     => paper    | rock, paper     => paper
  | scissors, paper => scissors | paper, scissors => scissors
  | a, _ => a
instance : Mul RPS := ⟨rpsMul⟩
instance : CommMagma RPS where
  mul_comm := by decide

-- `CommMagma` gives a commutative `*`:
#eval rock * paper
example (a b : RPS) : a * b = b * a := mul_comm a b
""")

E["Semigroup"] = ("LProj", r"""import Mathlib
/-- Left projection `a * b = a`: associative, but not commutative. -/
inductive LProj | x0 | x1
  deriving DecidableEq, Fintype, Repr
instance : Mul LProj := ⟨fun a _ => a⟩
instance : Semigroup LProj where
  mul_assoc := by decide

-- `Semigroup` gives associativity, so you may drop parentheses:
example (a b c : LProj) : a * b * c = a * (b * c) := mul_assoc a b c
""")

E["CommSemigroup"] = ("Konst", r"""import Mathlib
/-- The constant operation `a * b = k0`: associative and commutative, no identity. -/
inductive Konst | k0 | k1
  deriving DecidableEq, Fintype, Repr
instance : Mul Konst := ⟨fun _ _ => Konst.k0⟩
instance : CommSemigroup Konst where
  mul_assoc := by decide
  mul_comm := by decide

-- `CommSemigroup` gives both associativity and commutativity:
example (a b : Konst) : a * b = b * a := mul_comm a b
example (a b c : Konst) : a * b * c = a * (b * c) := mul_assoc a b c
""")

E["MulOneClass"] = ("RPSU", r"""import Mathlib
/-- Rock–Paper–Scissors with an adjoined unit `u`: has `1`, still not associative. -/
inductive RPSU | u | rr | pp | ss
  deriving DecidableEq, Fintype, Repr
open RPSU
def rpsuMul : RPSU → RPSU → RPSU
  | u, y => y
  | x, u => x
  | rr, ss => rr | ss, rr => rr
  | pp, rr => pp | rr, pp => pp
  | ss, pp => ss | pp, ss => ss
  | x, _ => x
instance : Mul RPSU := ⟨rpsuMul⟩
instance : One RPSU := ⟨u⟩
instance : MulOneClass RPSU where
  one_mul := by decide
  mul_one := by decide

-- `MulOneClass` gives a two-sided identity `1`:
#eval (1 : RPSU) * rr
example (a : RPSU) : 1 * a = a := one_mul a
example (a : RPSU) : a * 1 = a := mul_one a
""")

E["Monoid"] = ("M3", r"""import Mathlib
/-- `{e, a, b}` with `a`, `b` left zeros: an associative monoid, non-commutative. -/
inductive M3 | e | a | b
  deriving DecidableEq, Fintype, Repr
open M3
def m3mul : M3 → M3 → M3
  | e, y => y
  | x, e => x
  | a, _ => a
  | b, _ => b
instance : Mul M3 := ⟨m3mul⟩
instance : One M3 := ⟨e⟩
instance : Monoid M3 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  npow := npowRec

-- `Monoid` = associativity + `1`, so powers `a ^ n` are defined:
#eval a ^ 3
example (x : M3) : x ^ 2 = x * x := pow_two x
""")

E["CommMonoid"] = ("AndM", r"""import Mathlib
/-- `({⊥,⊤}, ∧)`: a commutative monoid with identity `⊤`; `⊥` has no inverse. -/
inductive AndM | ff | tt
  deriving DecidableEq, Fintype, Repr
open AndM
def andMul : AndM → AndM → AndM
  | tt, y => y
  | x, tt => x
  | ff, ff => ff
instance : Mul AndM := ⟨andMul⟩
instance : One AndM := ⟨tt⟩
instance : CommMonoid AndM where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  npow := npowRec

-- `CommMonoid`: a commutative, associative `*` with `1`:
#eval ff * tt
example (a b : AndM) : a * b = b * a := mul_comm a b
""")

E["DivInvMonoid"] = ("DIM", r"""import Mathlib
/-- A monoid with a formal `⁻¹ := id` (no inverse law): a `DivInvMonoid`, not a group. -/
inductive DIM | ff | tt
  deriving DecidableEq, Fintype, Repr
open DIM
def dimMul : DIM → DIM → DIM
  | tt, y => y
  | x, tt => x
  | ff, ff => ff
instance : Mul DIM := ⟨dimMul⟩
instance : One DIM := ⟨tt⟩
instance : Inv DIM := ⟨id⟩
instance : DivInvMonoid DIM where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  npow := npowRec
  zpow := zpowRec

-- `DivInvMonoid` provides `⁻¹`, `/` and `zpow`, with `a / b = a * b⁻¹`:
#eval tt / ff
example (a b : DIM) : a / b = a * b⁻¹ := div_eq_mul_inv a b
""")

E["MulZeroClass"] = ("RPS0", r"""import Mathlib
/-- Rock–Paper–Scissors with an absorbing `0`: `0` annihilates `*`, still not associative. -/
inductive RPS0 | zero | rock | paper | scissors
  deriving DecidableEq, Fintype, Repr
open RPS0
def rps0mul : RPS0 → RPS0 → RPS0
  | zero, _ => zero | _, zero => zero
  | rock, scissors => rock | scissors, rock => rock
  | paper, rock => paper | rock, paper => paper
  | scissors, paper => scissors | paper, scissors => scissors
  | x, _ => x
instance : Mul RPS0 := ⟨rps0mul⟩
instance : Zero RPS0 := ⟨zero⟩
instance : MulZeroClass RPS0 where
  zero_mul := by decide
  mul_zero := by decide

-- `MulZeroClass`: `0` is absorbing on both sides:
#eval (0 : RPS0) * rock
example (a : RPS0) : 0 * a = 0 := zero_mul a
example (a : RPS0) : a * 0 = 0 := mul_zero a
""")

E["MulZeroOneClass"] = ("RPSZ", r"""import Mathlib
/-- Rock–Paper–Scissors with both a `0` and a `1`: still not associative. -/
inductive RPSZ | zero | u | rock | paper | scissors
  deriving DecidableEq, Fintype, Repr
open RPSZ
def rpszmul : RPSZ → RPSZ → RPSZ
  | zero, _ => zero | _, zero => zero
  | u, y => y | x, u => x
  | rock, scissors => rock | scissors, rock => rock
  | paper, rock => paper | rock, paper => paper
  | scissors, paper => scissors | paper, scissors => scissors
  | x, _ => x
instance : Mul RPSZ := ⟨rpszmul⟩
instance : Zero RPSZ := ⟨zero⟩
instance : One RPSZ := ⟨u⟩
instance : MulZeroOneClass RPSZ where
  zero_mul := by decide
  mul_zero := by decide
  one_mul := by decide
  mul_one := by decide

-- `MulZeroOneClass` has both an absorbing `0` and an identity `1`:
#eval (0 : RPSZ) * rock
#eval (1 : RPSZ) * rock
example (a : RPSZ) : 0 * a = 0 := zero_mul a
example (a : RPSZ) : 1 * a = a := one_mul a
""")

E["SemigroupWithZero"] = ("LProj0", r"""import Mathlib
/-- Left projection with an absorbing `0`: associative with `0`, but no identity. -/
inductive LProj0 | zero | a | b
  deriving DecidableEq, Fintype, Repr
open LProj0
def lp0mul : LProj0 → LProj0 → LProj0
  | zero, _ => zero | _, zero => zero
  | x, _ => x
instance : Mul LProj0 := ⟨lp0mul⟩
instance : Zero LProj0 := ⟨zero⟩
instance : SemigroupWithZero LProj0 where
  mul_assoc := by decide
  zero_mul := by decide
  mul_zero := by decide

-- `SemigroupWithZero`: associative, with an absorbing `0`:
#eval (0 : LProj0) * a
example (x y z : LProj0) : x * y * z = x * (y * z) := mul_assoc x y z
example (x : LProj0) : 0 * x = 0 := zero_mul x
""")

E["MonoidWithZero"] = ("Nilp", r"""import Mathlib
/-- The nilpotent monoid `{0, 1, n}` with `n * n = 0`: `n ≠ 0` has no inverse. -/
inductive Nilp | zero | one | n
  deriving DecidableEq, Fintype, Repr
open Nilp
def nilpMul : Nilp → Nilp → Nilp
  | zero, _ => zero | _, zero => zero
  | one, y => y | x, one => x
  | n, n => zero
instance : Mul Nilp := ⟨nilpMul⟩
instance : Zero Nilp := ⟨zero⟩
instance : One Nilp := ⟨one⟩
instance : MonoidWithZero Nilp where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  npow := npowRec

-- `MonoidWithZero`: a monoid whose `0` absorbs; note `n` is nilpotent:
#eval n * n
example (x : Nilp) : 1 * x = x := one_mul x
example (x : Nilp) : x * 0 = 0 := mul_zero x
""")

E["GroupWithZero"] = ("GZ", r"""import Mathlib
/-- `0` adjoined to the cyclic group `C₃`: every nonzero element is a unit. -/
inductive GZ | zero | one | g | g2
  deriving DecidableEq, Fintype, Repr
open GZ
def gzMul : GZ → GZ → GZ
  | zero, _ => zero | _, zero => zero
  | one, y => y | x, one => x
  | g, g => g2 | g, g2 => one
  | g2, g => one | g2, g2 => g
def gzInv : GZ → GZ | zero => zero | one => one | g => g2 | g2 => g
instance : Mul GZ := ⟨gzMul⟩
instance : Zero GZ := ⟨zero⟩
instance : One GZ := ⟨one⟩
instance : Inv GZ := ⟨gzInv⟩
instance : GroupWithZero GZ where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  inv_zero := by decide
  mul_inv_cancel := by decide
  exists_pair_ne := ⟨zero, one, by decide⟩
  npow := npowRec
  zpow := zpowRec

-- `GroupWithZero`: every nonzero element has a multiplicative inverse:
#eval g * g⁻¹
example (x : GZ) (h : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ h
""")

E["AddCommMagma"] = ("ARPS", r"""import Mathlib
/-- Rock–Paper–Scissors written additively: `+` is commutative, but NOT associative. -/
inductive ARPS | a0 | a1 | a2
  deriving DecidableEq, Fintype, Repr
open ARPS
def arpsAdd : ARPS → ARPS → ARPS
  | a0, a2 => a0 | a2, a0 => a0
  | a1, a0 => a1 | a0, a1 => a1
  | a2, a1 => a2 | a1, a2 => a2
  | x, _ => x
instance : Add ARPS := ⟨arpsAdd⟩
instance : AddCommMagma ARPS where
  add_comm := by decide

-- `AddCommMagma` gives a commutative `+`:
#eval a0 + a2
example (a b : ARPS) : a + b = b + a := add_comm a b
""")

E["AddCommSemigroup"] = ("AKonst", r"""import Mathlib
/-- The constant operation `a + b = k0`: associative and commutative, but no zero. -/
inductive AKonst | k0 | k1
  deriving DecidableEq, Fintype, Repr
instance : Add AKonst := ⟨fun _ _ => AKonst.k0⟩
instance : AddCommSemigroup AKonst where
  add_assoc := by decide
  add_comm := by decide

-- `AddCommSemigroup` gives both associativity and commutativity of `+`:
example (a b : AKonst) : a + b = b + a := add_comm a b
example (a b c : AKonst) : a + b + c = a + (b + c) := add_assoc a b c
""")

E["AddCommMonoid"] = ("Cap", r"""import Mathlib
/-- A saturating counter `{0,1,2}` with `a + b = min (a + b) 2`: no negatives. -/
inductive Cap | c0 | c1 | c2
  deriving DecidableEq, Fintype, Repr
open Cap
def capAdd : Cap → Cap → Cap
  | c0, y => y | x, c0 => x
  | _, _ => c2
instance : Add Cap := ⟨capAdd⟩
instance : Zero Cap := ⟨c0⟩
instance : AddCommMonoid Cap where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  nsmul := nsmulRec

-- `AddCommMonoid`: a commutative, associative `+` with `0`:
#eval c1 + c2
example (a b : Cap) : a + b = b + a := add_comm a b
example (a : Cap) : 0 + a = a := zero_add a
""")

E["AddCommGroup"] = ("C3", r"""import Mathlib
/-- The cyclic group `C₃` written additively. -/
inductive C3 | z | a | b
  deriving DecidableEq, Fintype, Repr
open C3
def c3add : C3 → C3 → C3
  | z, y => y
  | x, z => x
  | a, a => b | a, b => z
  | b, a => z | b, b => a
def c3neg : C3 → C3 | z => z | a => b | b => a
instance : Add C3 := ⟨c3add⟩
instance : Zero C3 := ⟨z⟩
instance : Neg C3 := ⟨c3neg⟩
instance : AddCommGroup C3 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

-- `AddCommGroup`: `+` has inverses, so subtraction works:
#eval a - b
example (x : C3) : -x + x = 0 := neg_add_cancel x
example (a b : C3) : a - b = a + -b := sub_eq_add_neg a b
""")

E["CommSemiring"] = ("BSemi", r"""import Mathlib
/-- The Boolean semiring `(∨, ∧)`: distributive, but `⊤` has no additive inverse. -/
inductive BSemi | bot | top
  deriving DecidableEq, Fintype, Repr
open BSemi
def bAdd : BSemi → BSemi → BSemi
  | bot, y => y
  | x, bot => x
  | top, top => top
def bMul : BSemi → BSemi → BSemi
  | top, y => y
  | x, top => x
  | bot, bot => bot
instance : Add BSemi := ⟨bAdd⟩
instance : Mul BSemi := ⟨bMul⟩
instance : Zero BSemi := ⟨bot⟩
instance : One BSemi := ⟨top⟩
instance : CommSemiring BSemi where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  npow := npowRec

-- `CommSemiring`: `*` distributes over `+`, and both are commutative:
#eval top * (bot + top)
example (a b c : BSemi) : a * (b + c) = a * b + a * c := left_distrib a b c
""")

E["NonUnitalCommRing"] = ("Z2m", r"""import Mathlib
/-- `ℤ/2` additively, with the zero multiplication `x * y = 0`: a ring with no `1`. -/
inductive Z2m | zero | e
  deriving DecidableEq, Fintype, Repr
open Z2m
def z2add : Z2m → Z2m → Z2m
  | zero, y => y | x, zero => x | e, e => zero
instance : Add Z2m := ⟨z2add⟩
instance : Mul Z2m := ⟨fun _ _ => zero⟩
instance : Zero Z2m := ⟨zero⟩
instance : Neg Z2m := ⟨id⟩
instance : NonUnitalCommRing Z2m where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

-- `NonUnitalCommRing`: an additive group with a distributive, commutative `*` (no `1`):
#eval e * e
example (a b : Z2m) : a * b = b * a := mul_comm a b
example (a : Z2m) : -a + a = 0 := neg_add_cancel a
""")

E["Ring"] = ("UT", r"""import Mathlib
/-- Upper-triangular `2×2` matrices over `𝔽₂`: `⟨a,b,d⟩ = [[a,b],[0,d]]`. Non-commutative. -/
structure UT where
  a : Bool
  b : Bool
  d : Bool
deriving DecidableEq, Fintype, Repr
instance : Add UT := ⟨fun x y => ⟨xor x.a y.a, xor x.b y.b, xor x.d y.d⟩⟩
instance : Mul UT := ⟨fun x y => ⟨x.a && y.a, xor (x.a && y.b) (x.b && y.d), x.d && y.d⟩⟩
instance : Zero UT := ⟨⟨false, false, false⟩⟩
instance : One UT := ⟨⟨true, false, true⟩⟩
instance : Neg UT := ⟨id⟩
instance : Ring UT where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

-- `Ring`: associative `*` distributing over an additive group (order matters here):
#eval (⟨true, true, false⟩ : UT) * ⟨false, false, true⟩
example (a b c : UT) : a * (b + c) = a * b + a * c := left_distrib a b c
example (a b c : UT) : a * b * c = a * (b * c) := mul_assoc a b c
""")

E["CommRing"] = ("Z4", r"""import Mathlib
/-- `ℤ/4` from scratch: a commutative ring with zero divisors (`2 * 2 = 0`). -/
structure Z4 where val : Fin 4
deriving DecidableEq, Fintype, Repr
instance : Add Z4 := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Mul Z4 := ⟨fun x y => ⟨x.val * y.val⟩⟩
instance : Zero Z4 := ⟨⟨0⟩⟩
instance : One Z4 := ⟨⟨1⟩⟩
instance : Neg Z4 := ⟨fun x => ⟨-x.val⟩⟩
instance : CommRing Z4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

-- `CommRing`: a commutative ring — full arithmetic with `+`, `-`, `*`:
#eval (⟨2⟩ : Z4) * ⟨3⟩
example (a b : Z4) : a * b = b * a := mul_comm a b
example (a b : Z4) : a - b = a + -b := sub_eq_add_neg a b
""")

E["Field"] = ("GF2", r"""import Mathlib
/-- The two-element field `𝔽₂ = ({0,1}, ⊕, ∧)`. -/
inductive GF2 | o | l
  deriving DecidableEq, Fintype, Repr
open GF2
def gf2add : GF2 → GF2 → GF2 | o, y => y | x, o => x | l, l => o
def gf2mul : GF2 → GF2 → GF2 | l, l => l | _, _ => o
instance : Add GF2 := ⟨gf2add⟩
instance : Mul GF2 := ⟨gf2mul⟩
instance : Zero GF2 := ⟨o⟩
instance : One GF2 := ⟨l⟩
instance : Neg GF2 := ⟨id⟩
instance : Inv GF2 := ⟨id⟩
instance : CommRing GF2 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
noncomputable instance : Field GF2 := by
  refine { (inferInstance : CommRing GF2) with
    inv := fun x => x⁻¹,
    exists_pair_ne := ⟨o, l, by decide⟩,
    mul_inv_cancel := ?_, inv_zero := by decide,
    nnqsmul := _, qsmul := _ }
  decide

-- `Field`: every nonzero element is invertible:
example (x : GF2) (h : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ h
""")

out = {node: {"disp": disp, "code": code} for node, (disp, code) in E.items()}
here = os.path.dirname(os.path.abspath(__file__))
dest = os.path.join(here, "..", "site", "finite_exemplars.json")
with open(dest, "w") as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print(f"wrote {len(out)} exemplars to {os.path.normpath(dest)}")
