import Mathlib.Tactic

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.cdot false
set_option linter.style.multiGoal false

namespace Chapter2

/--
  Assumption 2.6 (Existence of natural numbers).  Here we use an explicit construction of the
  natural numbers (using an inductive type).  For a more axiomatic approach, see the epilogue to
  this chapter.
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`

/-- Axiom 2.1 (0 is a natural number) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩
#check (0:Nat)

/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)


/--
  Definition 2.1.3 (Definition of the numerals 0, 1, 2, etc.). Note: to avoid ambiguity, one may
  need to use explicit casts such as (0:Nat), (1:Nat), etc. to refer to this chapter's version of
  the natural numbers.
-/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨ 1 ⟩

@[grind]
lemma Nat.zero_succ : 0++ = 1 := by rfl
#check (1:Nat)

lemma Nat.one_succ : 1++ = 2 := by rfl
#check (2:Nat)

/-- Proposition 2.1.4 (3 is a natural number)-/
lemma Nat.two_succ : 2++ = 3 := by rfl
#check (3:Nat)

theorem Nat.succ_ne (n:Nat) : n++ ≠ 0 := by grind

theorem Nat.four_ne : (4:Nat) ≠ 0 := by grind

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's `Nat.succ_inj`.
-/
@[grind]
theorem Nat.succ_cancel {n m:Nat} (hnm: n++ = m++) : n = m := by grind

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's `Nat.succ_ne_succ`.
-/
theorem Nat.succ_ne_succ (n m:Nat) : n ≠ m → n++ ≠ m++ := by grind

/-- Proposition 2.1.8 (6 is not equal to 2) -/
theorem Nat.six_ne_two : (6:Nat) ≠ 2 := by
-- this proof is written to follow the structure of the original text.
  by_contra h
  replace h := succ_cancel h
  grind

/-- One can also prove this sort of result by the `decide` tactic -/
theorem Nat.six_ne_two' : (6:Nat) ≠ 2 := by
  decide

/--
  Axiom 2.5 (Principle of mathematical induction). The `induction` (or `induction'`) tactic in
  Mathlib serves as a substitute for this axiom.
-/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

/--
  Recursion. Analogous to the inbuilt Mathlib method `Nat.rec` associated to
  the Mathlib natural numbers
-/
abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (recurse f c n)

theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl

theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) :
    recurse f c (n++) = f n (recurse f c n) := by rfl

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    -- this proof is written to follow the structure of the original text.
    apply funext; apply induction
    . exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor
  . exact recurse_zero _ _
  exact recurse_succ _ _


/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_uniq (f: Nat → Nat → Nat) (c: Nat) :
    ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  . constructor
    . exact recurse_zero _ _
    . exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

@[simp, grind =]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

@[grind =]
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

@[grind =]
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

@[grind =]
theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by decide

@[simp, grind=]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction
  · grind
  · grind

@[grind =]
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  revert n; apply induction
  · grind
  · grind

@[grind =]
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  rw [show 1 = 0++ from rfl]
  grind

@[grind =]
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  revert n; apply induction
  · grind
  · grind

@[grind =]
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert a; apply induction
  . grind
  . grind

theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  revert a; apply induction
  · grind
  · grind


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid.
This permits tactics such as `abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

@[grind]
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  rw [add_comm]
  exact add_pos_left _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).IsPos := add_pos_left _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).IsPos := add_pos_right _ hb
  tauto

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  sorry

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `≤` notation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le`. -/
@[symm]
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt`. -/
@[symm]
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

@[grind]
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

theorem Nat.self_ne_succ (n:Nat) : n ≠ n++ := by
  revert n; apply induction
  grind
  grind

/-- Compare with Mathlib's `Nat.lt_succ_self`. -/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  constructor
  use 1, by grind
  exact self_ne_succ n

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0
  grind

@[refl]
theorem Nat.le_refl (a:Nat) : a ≤ a := a.ge_refl

/-- The refl tag allows for the `rfl` tactic to work for inequalities. -/
example (a b:Nat): a+b ≥ a+b := by rfl

@[grind]
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  sorry

@[grind]
theorem Nat.le_trans {a b c:Nat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

@[grind]
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  sorry

@[grind]
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  sorry

@[grind]
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

@[grind]
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

@[grind]
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  sorry

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  sorry

@[grind]
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

@[grind]
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (le_of_lt h.1) (le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

@[grind]
theorem Nat.not_lt_self {a: Nat} (h : a < a) : False := by
  apply not_lt_of_gt a a
  simp [h]

@[grind]
theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  rcases hab with ⟨d, hd⟩
  grind

/-- This lemma was a `why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  use a
  grind

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous`.  Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := b.zero_le
    replace why := (le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by sorry
    tauto
  have why : a++ > b := by sorry
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    sorry
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        sorry
      | isFalse h =>
        apply isTrue
        sorry
    | isFalse h =>
      apply isFalse
      sorry

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

/-- (Not from textbook) Nat has the structure of a linear ordering. This allows for tactics
such as `order` and `calc` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge := by
    intro a b
    constructor
    intro h
    constructor
    . grind
    . by_contra h'
      exact not_lt_self (lt_of_le_of_lt h' h)

    rintro ⟨ h1, h2 ⟩
    rw [lt_iff, ← le_iff]
    grind
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := by
    intro a b
    obtain h | h | h := trichotomous a b
    . left; exact le_of_lt h
    . simp [h, ge_refl]
    . right; exact le_of_lt h
  toDecidableLE := decidableRel

/-- This illustration of the `order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- An illustration of the `calc` tactic with `≤/<`. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

/-- (Not from textbook) Nat has the structure of an ordered monoid. This allows for tactics
such as `gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by grind

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a + d ≤ c + e := by
  gcongr
  order

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  sorry

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  sorry

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the `*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

@[grind =]
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

@[grind =]
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

@[grind =]
theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ]
  grind

@[grind =]
theorem Nat.one_mul (m: Nat) : 1 * m = m := by grind

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ]
  grind

@[grind =]
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n; apply induction
  grind
  grind

@[grind =]
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  grind
  grind

@[grind =]
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert m; apply induction
  grind
  grind

@[grind =]
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  grind

@[grind]
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  revert n; apply induction
  grind
  grind

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's `Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  intro h
  by_contra hnm
  rw [not_or] at hnm
  rcases hnm with ⟨ hn, hm ⟩
  . have := pos_mul_pos hn hm
    exact this h

  grind

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's `Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  · grind
  · grind

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's `Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's `Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  sorry

/-- (Not from textbook)  Nat is a commutative semiring.
    This allows tactics such as `ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the `ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring

@[grind]
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

@[grind]
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

@[grind]
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  grind

theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's `Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  grind

/-- (Not from textbook) Nat is an ordered semiring.
This allows tactics such as `gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by sorry
  mul_le_mul_of_nonneg_left := by sorry
  mul_le_mul_of_nonneg_right := by sorry

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's `Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  sorry

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's `Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's `Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's `Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  sorry

end Chapter2
