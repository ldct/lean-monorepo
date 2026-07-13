import Mathlib

/-!
# A finite zoo for the algebra hierarchy

For each node on the algebra spine of the `normedfield_hierarchy` graph, this file
builds a **small finite structure that sits exactly at that node** — it satisfies the
node's axioms but characteristically fails the next axiom up.  The motivating example
is the Rock–Paper–Scissors magma: commutative but *not* associative, so it is a
`CommMagma` and nothing more.

Every carrier is a fresh `inductive`/`structure` (never `Fin n` directly, whose
Mathlib arithmetic instances would clash), deriving `DecidableEq, Fintype`.  Because
the carriers are finite and their operations compute, **every axiom — and every
characteristic non-axiom (⊣) — is proved by `decide`.**

Compile with:  `lake env lean Playground/FiniteExemplars.lean`

The four ladders below trace the graph's spine.  `A ⊣ B` = "sits at `A`, fails `B`".

Part I  — multiplicative, no zero
  Mag2   Mul (bare magma)     ⊣ commutativity, associativity  (material nonimpl.)
  RPS    CommMagma            ⊣ associativity                 (rock/paper/scissors)
  LProj  Semigroup            ⊣ commutativity                 (a·b = a)
  Konst  CommSemigroup        ⊣ has no identity               (a·b = k)
  RPSU   MulOneClass          ⊣ associativity                 (RPS + a unit)
  M3     Monoid               ⊣ commutativity, invertibility  (e + two left zeros)
  AndM   CommMonoid           ⊣ invertibility                 ({⊥,⊤}, ∧)
  DIM    DivInvMonoid         ⊣ inverse law                   (∧-monoid, inv := id)
  D3     Group, non-abelian   ⊣ commutativity                 (dihedral D₃ ≅ S₃) †

Part II — multiplicative, with an absorbing zero
  RPS0   MulZeroClass         ⊣ associativity                 (RPS + 0)
  RPSZ   MulZeroOneClass      ⊣ associativity                 (RPS + 0 + 1)
  LProj0 SemigroupWithZero    ⊣ has no identity               (a·b = a, + 0)
  Nilp   MonoidWithZero       ⊣ invertibility (n·n = 0)       (nilpotent {0,1,n})
  GZ     GroupWithZero        ⊣ (has no addition; not a ring) (0 ⊔ C₃)

Part III — additive
  ARPS   AddCommMagma         ⊣ associativity                 (RPS, written additively)
  AKonst AddCommSemigroup     ⊣ has no zero                   (a+b = k, additively)
  Cap    AddCommMonoid        ⊣ negation                      (saturating {0,1,2})
  AD3    AddGroup, non-abelian ⊣ commutativity                (dihedral D₃, additively)
  C3     AddCommGroup                                          (cyclic C₃)
  Z3     AddGroupWithOne      ⊣ (has no multiplication)       (ℤ/3: +, −, 1, ℤ-casts)

Part IV — distributive: semirings, rings, fields
  BSemi  CommSemiring         ⊣ additive negation             (Boolean semiring ∨,∧)
  Z2m    NonUnitalCommRing    ⊣ has no unit                   (ℤ/2 with x·y = 0)
  UT     Ring, non-commutative ⊣ commutativity                (upper-tri 2×2 / 𝔽₂)
  Z4     CommRing             ⊣ no zero divisors (2·2 = 0)    (ℤ/4)
  GF2    Field                                                 (𝔽₂ = ⊕,∧)

† The spine's multiplicative structure runs `Mul → … → Monoid → MonoidWithZero →
  GroupWithZero` (a field has a `0`), so plain `Group`/`CommGroup` are *not* graph
  nodes.  `D3` is the finite non-abelian witness, showing `Monoid`/`DivInvMonoid`
  non-commutatively; `UT` does the same for `Ring`.
-/

namespace FiniteExemplars

/-! ## Part I — the multiplicative ladder (no zero) -/

/-! ### Mag2 — bare magma (`Mul`, no laws): material nonimplication `a·b = a ∧ ¬b` -/

inductive Mag2 | ff | tt
deriving DecidableEq, Fintype, Repr
open Mag2 in
private def mag2mul : Mag2 → Mag2 → Mag2
  | tt, ff => tt
  | _,  _  => ff
instance : Mul Mag2 := ⟨mag2mul⟩

example : ¬ ∀ a b : Mag2, a * b = b * a := by decide            -- ⊣ not commutative
example : ¬ ∀ a b c : Mag2, (a * b) * c = a * (b * c) := by decide  -- ⊣ not associative

/-! ### RPS — `CommMagma` (Rock–Paper–Scissors, the poster child) -/

inductive RPS | rock | paper | scissors
deriving DecidableEq, Fintype, Repr
open RPS in
/-- `a · b` = the winner (rock⊳scissors, paper⊳rock, scissors⊳paper); ties pick `a`. -/
private def rpsMul : RPS → RPS → RPS
  | rock, scissors => rock     | scissors, rock => rock
  | paper, rock     => paper    | rock, paper     => paper
  | scissors, paper => scissors | paper, scissors => scissors
  | a, _ => a
instance : Mul RPS := ⟨rpsMul⟩

instance : CommMagma RPS where
  mul_comm := by decide

example : ¬ ∀ a b c : RPS, (a * b) * c = a * (b * c) := by decide  -- ⊣ not associative

/-! ### LProj — `Semigroup`: left projection `a·b = a` (assoc, not comm) -/

inductive LProj | x0 | x1
deriving DecidableEq, Fintype, Repr
instance : Mul LProj := ⟨fun a _ => a⟩

instance : Semigroup LProj where
  mul_assoc := by decide

example : ¬ ∀ a b : LProj, a * b = b * a := by decide  -- ⊣ not commutative

/-! ### Konst — `CommSemigroup`: constant `a·b = k0` (assoc + comm, no identity) -/

inductive Konst | k0 | k1
deriving DecidableEq, Fintype, Repr
instance : Mul Konst := ⟨fun _ _ => Konst.k0⟩

instance : CommSemigroup Konst where
  mul_assoc := by decide
  mul_comm := by decide

example : ¬ ∃ e : Konst, ∀ x : Konst, e * x = x ∧ x * e = x := by decide  -- ⊣ no identity

/-! ### RPSU — `MulOneClass`: RPS with an adjoined unit (unital, still not assoc) -/

inductive RPSU | u | rr | pp | ss
deriving DecidableEq, Fintype, Repr
open RPSU in
private def rpsuMul : RPSU → RPSU → RPSU
  | u, y => y
  | x, u => x
  | rr, ss => rr | ss, rr => rr
  | pp, rr => pp | rr, pp => pp
  | ss, pp => ss | pp, ss => ss
  | x, _ => x
instance : Mul RPSU := ⟨rpsuMul⟩
instance : One RPSU := ⟨RPSU.u⟩

instance : MulOneClass RPSU where
  one_mul := by decide
  mul_one := by decide

example : ¬ ∀ a b c : RPSU, (a * b) * c = a * (b * c) := by decide  -- ⊣ not associative

/-! ### M3 — `Monoid`: {e, a, b} with `a`, `b` left zeros (non-comm, not a group) -/

inductive M3 | e | a | b
deriving DecidableEq, Fintype, Repr
open M3 in
private def m3mul : M3 → M3 → M3
  | e, y => y
  | x, e => x
  | a, _ => a
  | b, _ => b
instance : Mul M3 := ⟨m3mul⟩
instance : One M3 := ⟨M3.e⟩

instance : Monoid M3 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  npow := npowRec

example : ¬ ∀ x y : M3, x * y = y * x := by decide                  -- ⊣ not commutative
example : ¬ ∃ i : M3, M3.a * i = 1 ∧ i * M3.a = 1 := by decide      -- ⊣ `a` has no inverse

/-! ### AndM — `CommMonoid`: ({⊥,⊤}, ∧) (identity ⊤, `⊥` has no inverse) -/

inductive AndM | ff | tt
deriving DecidableEq, Fintype, Repr
open AndM in
private def andMul : AndM → AndM → AndM
  | tt, y => y
  | x, tt => x
  | ff, ff => ff
instance : Mul AndM := ⟨andMul⟩
instance : One AndM := ⟨AndM.tt⟩

instance : CommMonoid AndM where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  npow := npowRec

example : ¬ ∃ i : AndM, AndM.ff * i = 1 := by decide  -- ⊣ `ff` has no inverse

/-! ### DIM — `DivInvMonoid`: a monoid with a formal `⁻¹` that is *not* an inverse

`DivInvMonoid` adds `Inv`/`Div` (with `zpow`) to a monoid but imposes **no** inverse
law, so any monoid with `inv := id` inhabits it without being a group. -/

inductive DIM | ff | tt
deriving DecidableEq, Fintype, Repr
open DIM in
private def dimMul : DIM → DIM → DIM
  | tt, y => y
  | x, tt => x
  | ff, ff => ff
instance : Mul DIM := ⟨dimMul⟩
instance : One DIM := ⟨DIM.tt⟩
instance : Inv DIM := ⟨id⟩

instance : DivInvMonoid DIM where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  npow := npowRec
  zpow := zpowRec

example : ¬ ∃ i : DIM, DIM.ff * i = 1 := by decide  -- ⊣ `ff` has no inverse (not a group)

/-! ### D3 — a non-abelian `Group`: the dihedral/symmetric group `D₃ ≅ S₃`

Off the normed-field spine (see the header note), included as the finite non-abelian
witness.  Elements are `(rot, flip)` with the semidirect-product multiplication;
`rot : Fin 3` is used purely as *data* to define a fresh operation. -/

structure D3 where
  rot : Fin 3
  flip : Bool
deriving DecidableEq, Fintype, Repr

private def d3mul (x y : D3) : D3 :=
  ⟨x.rot + (if x.flip then -y.rot else y.rot), xor x.flip y.flip⟩
private def d3inv (x : D3) : D3 :=
  ⟨if x.flip then x.rot else -x.rot, x.flip⟩
instance : Mul D3 := ⟨d3mul⟩
instance : One D3 := ⟨⟨0, false⟩⟩
instance : Inv D3 := ⟨d3inv⟩

instance : Group D3 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  npow := npowRec
  zpow := zpowRec

example : ¬ ∀ x y : D3, x * y = y * x := by decide  -- ⊣ non-abelian

/-! ## Part II — the multiplicative ladder with an absorbing zero -/

/-! ### RPS0 — `MulZeroClass`: RPS plus an absorbing `0` (still not associative) -/

inductive RPS0 | zero | rock | paper | scissors
deriving DecidableEq, Fintype, Repr
open RPS0 in
private def rps0mul : RPS0 → RPS0 → RPS0
  | zero, _ => zero | _, zero => zero
  | rock, scissors => rock | scissors, rock => rock
  | paper, rock => paper | rock, paper => paper
  | scissors, paper => scissors | paper, scissors => scissors
  | x, _ => x
instance : Mul RPS0 := ⟨rps0mul⟩
instance : Zero RPS0 := ⟨RPS0.zero⟩

instance : MulZeroClass RPS0 where
  zero_mul := by decide
  mul_zero := by decide

example : ¬ ∀ a b c : RPS0, (a * b) * c = a * (b * c) := by decide  -- ⊣ not associative

/-! ### RPSZ — `MulZeroOneClass`: RPS plus both a `0` and a `1` (still not associative) -/

inductive RPSZ | zero | u | rock | paper | scissors
deriving DecidableEq, Fintype, Repr
open RPSZ in
private def rpszmul : RPSZ → RPSZ → RPSZ
  | zero, _ => zero | _, zero => zero
  | u, y => y | x, u => x
  | rock, scissors => rock | scissors, rock => rock
  | paper, rock => paper | rock, paper => paper
  | scissors, paper => scissors | paper, scissors => scissors
  | x, _ => x
instance : Mul RPSZ := ⟨rpszmul⟩
instance : Zero RPSZ := ⟨RPSZ.zero⟩
instance : One RPSZ := ⟨RPSZ.u⟩

instance : MulZeroOneClass RPSZ where
  zero_mul := by decide
  mul_zero := by decide
  one_mul := by decide
  mul_one := by decide

example : ¬ ∀ a b c : RPSZ, (a * b) * c = a * (b * c) := by decide  -- ⊣ not associative

/-! ### LProj0 — `SemigroupWithZero`: left projection with an absorbing `0` (no identity) -/

inductive LProj0 | zero | a | b
deriving DecidableEq, Fintype, Repr
open LProj0 in
private def lp0mul : LProj0 → LProj0 → LProj0
  | zero, _ => zero | _, zero => zero
  | x, _ => x
instance : Mul LProj0 := ⟨lp0mul⟩
instance : Zero LProj0 := ⟨LProj0.zero⟩

instance : SemigroupWithZero LProj0 where
  mul_assoc := by decide
  zero_mul := by decide
  mul_zero := by decide

example : ¬ ∃ e : LProj0, ∀ x : LProj0, e * x = x ∧ x * e = x := by decide  -- ⊣ no identity

/-! ### Nilp — `MonoidWithZero`: nilpotent monoid `{0, 1, n}` with `n·n = 0` -/

inductive Nilp | zero | one | n
deriving DecidableEq, Fintype, Repr
open Nilp in
private def nilpMul : Nilp → Nilp → Nilp
  | zero, _ => zero | _, zero => zero
  | one, y => y | x, one => x
  | n, n => zero
instance : Mul Nilp := ⟨nilpMul⟩
instance : Zero Nilp := ⟨Nilp.zero⟩
instance : One Nilp := ⟨Nilp.one⟩

instance : MonoidWithZero Nilp where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  npow := npowRec

example : ¬ ∃ i : Nilp, Nilp.n * i = 1 := by decide  -- ⊣ `n ≠ 0` has no inverse (not GroupWithZero)

/-! ### GZ — `GroupWithZero`: `0` adjoined to the cyclic group `C₃`

Every nonzero element is a unit, and there is a `0`, but the carrier has no addition
at all — so it is a `GroupWithZero` that underlies no field. -/

inductive GZ | zero | one | g | g2
deriving DecidableEq, Fintype, Repr
open GZ in
private def gzMul : GZ → GZ → GZ
  | zero, _ => zero | _, zero => zero
  | one, y => y | x, one => x
  | g, g => g2 | g, g2 => one
  | g2, g => one | g2, g2 => g
open GZ in
private def gzInv : GZ → GZ | zero => zero | one => one | g => g2 | g2 => g
instance : Mul GZ := ⟨gzMul⟩
instance : Zero GZ := ⟨GZ.zero⟩
instance : One GZ := ⟨GZ.one⟩
instance : Inv GZ := ⟨gzInv⟩

instance : GroupWithZero GZ where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  inv_zero := by decide
  mul_inv_cancel := by decide
  exists_pair_ne := ⟨GZ.zero, GZ.one, by decide⟩
  npow := npowRec
  zpow := zpowRec

-- every nonzero element is invertible, by decide:
example : ∀ x : GZ, x ≠ 0 → x * x⁻¹ = 1 := by decide

/-! ## Part III — the additive ladder

The multiplicative ladder of Part I has a `to_additive` mirror; these are the
lower additive rungs (the top two, `AddCommMonoid`/`AddCommGroup`, follow). -/

/-! ### ARPS — `AddCommMagma`: Rock–Paper–Scissors written additively (comm, not assoc) -/

inductive ARPS | a0 | a1 | a2
deriving DecidableEq, Fintype, Repr
open ARPS in
private def arpsAdd : ARPS → ARPS → ARPS
  | a0, a2 => a0 | a2, a0 => a0
  | a1, a0 => a1 | a0, a1 => a1
  | a2, a1 => a2 | a1, a2 => a2
  | x, _ => x
instance : Add ARPS := ⟨arpsAdd⟩

instance : AddCommMagma ARPS where
  add_comm := by decide

example : ¬ ∀ a b c : ARPS, (a + b) + c = a + (b + c) := by decide  -- ⊣ not associative

/-! ### AKonst — `AddCommSemigroup`: constant `a + b = k0` (assoc + comm, no zero) -/

inductive AKonst | k0 | k1
deriving DecidableEq, Fintype, Repr
instance : Add AKonst := ⟨fun _ _ => AKonst.k0⟩

instance : AddCommSemigroup AKonst where
  add_assoc := by decide
  add_comm := by decide

example : ¬ ∃ z : AKonst, ∀ x : AKonst, z + x = x ∧ x + z = x := by decide  -- ⊣ no zero

/-! ### Cap — `AddCommMonoid`: saturating counter `{0,1,2}`, `a + b = min(a+b, 2)` -/

inductive Cap | c0 | c1 | c2
deriving DecidableEq, Fintype, Repr
open Cap in
private def capAdd : Cap → Cap → Cap
  | c0, y => y | x, c0 => x
  | _, _ => c2
instance : Add Cap := ⟨capAdd⟩
instance : Zero Cap := ⟨Cap.c0⟩

instance : AddCommMonoid Cap where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  nsmul := nsmulRec

example : ¬ ∃ y : Cap, Cap.c1 + y = 0 := by decide  -- ⊣ `1` has no negative (not AddGroup)

/-! ### AD3 — a non-abelian `AddGroup`: the dihedral group `D₃`, written additively

The additive rendering of the `D3` group from Part I — `+` has inverses but does
not commute. (Additive notation for a non-abelian group is unconventional, but
`AddGroup` genuinely does not assume commutativity.) -/

structure AD3 where
  rot : Fin 3
  flip : Bool
deriving DecidableEq, Fintype, Repr

private def ad3add (x y : AD3) : AD3 :=
  ⟨x.rot + (if x.flip then -y.rot else y.rot), xor x.flip y.flip⟩
private def ad3neg (x : AD3) : AD3 :=
  ⟨if x.flip then x.rot else -x.rot, x.flip⟩
instance : Add AD3 := ⟨ad3add⟩
instance : Zero AD3 := ⟨⟨0, false⟩⟩
instance : Neg AD3 := ⟨ad3neg⟩

instance : AddGroup AD3 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

example : ¬ ∀ x y : AD3, x + y = y + x := by decide  -- ⊣ non-abelian

/-! ### C3 — `AddCommGroup`: the cyclic group `C₃` (written additively) -/

inductive C3 | z | a | b
deriving DecidableEq, Fintype, Repr
open C3 in
private def c3add : C3 → C3 → C3
  | z, y => y
  | x, z => x
  | a, a => b | a, b => z
  | b, a => z | b, b => a
open C3 in
private def c3neg : C3 → C3 | z => z | a => b | b => a
instance : Add C3 := ⟨c3add⟩
instance : Zero C3 := ⟨C3.z⟩
instance : Neg C3 := ⟨c3neg⟩

instance : AddCommGroup C3 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Z3 — `AddGroupWithOne`: `ℤ/3` as `+`, `−`, a `1`, and `ℕ`/`ℤ`-casts (no `*`)

The additive backbone of a ring: an additive group with a distinguished `1` and
the resulting `ℕ`/`ℤ`-casts `n ↦ n • 1` — but *no* multiplication.  The cast laws
range over all of `ℕ`/`ℤ`, so they are not `decide`-able; they hold by the
recursive `Nat.unaryCast`/`Int.castDef` defaults, leaving only the finite
additive-group axioms for `decide`. -/

inductive Z3 | z | o | t
deriving DecidableEq, Fintype, Repr
open Z3 in
private def z3add : Z3 → Z3 → Z3
  | z, y => y | x, z => x
  | o, o => t | o, t => z
  | t, o => z | t, t => o
open Z3 in
private def z3neg : Z3 → Z3 | z => z | o => t | t => o
instance : Add Z3 := ⟨z3add⟩
instance : Zero Z3 := ⟨Z3.z⟩
instance : Neg Z3 := ⟨z3neg⟩

instance : AddGroupWithOne Z3 where
  one := Z3.o
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

-- concrete casts still evaluate, so `decide` checks them (`3 = 0`, `2 = -1` in ℤ/3):
example : ((3 : ℤ) : Z3) = 0 := by decide
example : ((2 : ℤ) : Z3) = -1 := by decide

/-! ## Part IV — distributive structures: semirings, rings, fields -/

/-! ### BSemi — `CommSemiring`: the Boolean semiring `(∨, ∧)` (no additive inverses) -/

inductive BSemi | bot | top
deriving DecidableEq, Fintype, Repr
open BSemi in
private def bAdd : BSemi → BSemi → BSemi
  | bot, y => y
  | x, bot => x
  | top, top => top
open BSemi in
private def bMul : BSemi → BSemi → BSemi
  | top, y => y
  | x, top => x
  | bot, bot => bot
instance : Add BSemi := ⟨bAdd⟩
instance : Mul BSemi := ⟨bMul⟩
instance : Zero BSemi := ⟨BSemi.bot⟩
instance : One BSemi := ⟨BSemi.top⟩

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

example : ¬ ∃ y : BSemi, BSemi.top + y = 0 := by decide  -- ⊣ `top` has no additive inverse

/-! ### Z2m — `NonUnitalCommRing`: `ℤ/2` additively with the **zero multiplication**

Distributive and associative with a full additive group, but the multiplication is
constantly `0`, so on ≥ 2 elements there is no multiplicative identity — a ring
without a `1`. -/

inductive Z2m | zero | e
deriving DecidableEq, Fintype, Repr
open Z2m in
private def z2add : Z2m → Z2m → Z2m
  | zero, y => y | x, zero => x | e, e => zero
instance : Add Z2m := ⟨z2add⟩
instance : Mul Z2m := ⟨fun _ _ => Z2m.zero⟩
instance : Zero Z2m := ⟨Z2m.zero⟩
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

example : ¬ ∃ o : Z2m, ∀ x : Z2m, o * x = x ∧ x * o = x := by decide  -- ⊣ no multiplicative unit

/-! ### UT — a non-commutative `Ring`: upper-triangular `2×2` matrices over `𝔽₂`

`⟨a, b, d⟩` is the matrix `[[a, b], [0, d]]` (8 elements); `+` is componentwise xor,
`*` is matrix multiplication over `𝔽₂` (`&&` for `·`, `xor` for `+`). -/

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

example : ¬ ∀ x y : UT, x * y = y * x := by decide  -- ⊣ non-commutative

/-! ### Z4 — `CommRing` with zero divisors: `ℤ/4` from scratch (not a domain, not a field) -/

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

example : (⟨2⟩ : Z4) * ⟨2⟩ = 0 ∧ (⟨2⟩ : Z4) ≠ 0 := by decide         -- ⊣ a zero divisor
example : ¬ ∀ x y : Z4, x * y = 0 → x = 0 ∨ y = 0 := by decide        --   ⇒ not a domain

/-! ### GF2 — `Field`: the two-element field `𝔽₂ = ({0,1}, ⊕, ∧)` -/

inductive GF2 | o | l
deriving DecidableEq, Fintype, Repr
open GF2 in
private def gf2add : GF2 → GF2 → GF2 | o, y => y | x, o => x | l, l => o
open GF2 in
private def gf2mul : GF2 → GF2 → GF2 | l, l => l | _, _ => o
instance : Add GF2 := ⟨gf2add⟩
instance : Mul GF2 := ⟨gf2mul⟩
instance : Zero GF2 := ⟨GF2.o⟩
instance : One GF2 := ⟨GF2.l⟩
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
    exists_pair_ne := ⟨GF2.o, GF2.l, by decide⟩,
    mul_inv_cancel := ?_, inv_zero := by decide,
    nnqsmul := _, qsmul := _ }
  decide

-- every nonzero element is a unit (the field property), by decide:
example : ∀ x : GF2, x ≠ 0 → x * x⁻¹ = 1 := by decide

end FiniteExemplars
