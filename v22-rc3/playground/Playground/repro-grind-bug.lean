import Mathlib

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro ⟨a, b⟩
      rw [Nat.add_left_cancel_iff]
    symm := by
      intro ⟨a, b⟩ ⟨c, d⟩ h
      linarith
    trans := by
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      have h3 := congrArg₂ (· + ·) h1 h2
      simp at h3
      omega
    }

@[simp]
theorem PreInt.equiv (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

/--
(a+b) —— (b+c) ≃ (a+d) —— (d+c)
-/
example (a b c d: ℕ) : (⟨ a + b, b + c ⟩ : PreInt) ≈ (⟨ a + d, d + c ⟩ : PreInt) := by
  rw [PreInt.equiv]
  omega

example : 3 + 5 = 5 + 3 := rfl

def five_minus_three : PreInt := ⟨ 5, 3 ⟩
def six_minus_four : PreInt := ⟨ 6, 4 ⟩
def six_minus_three : PreInt := ⟨ 6, 3 ⟩
example : five_minus_three ≈ six_minus_four := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ) : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
@[simp high, grind]
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp at *
    omega
)

/-- Note: the operator precedence is parsed as (a —— b) + (c —— d)  -/
@[simp, grind]
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

theorem Int.add_comm : ∀ a b: Int, a + b = b + a := by
    intro a b
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp
    omega

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp high]
theorem Int.natCast_inj (n m:ℕ) :
    (n : Int) = (m : Int) ↔ n = m := by
      simp only [natCast_eq, eq, add_zero]

@[grind]
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor
  intro h
  rw [show (0 : Int) = ((0 : Nat) : Int) by rfl] at h
  rw [natCast_inj] at h
  exact h
  intro h
  rw [h]
  simp


/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro a b h
    dsimp
    rw [Int.eq]
    whnf at h
    linarith
  )

@[simp]
theorem Int.neg_eq (a b:ℕ) : -(a——b) = b——a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n


@[simp]
theorem Int.eq_0' (a b : ℕ) : a——b = 0 ↔ a = b := by
  rw [show (0 : Int) = 0 —— 0 by rfl]
  constructor
  intro h
  simp at h
  omega
  intro h
  rw [h, eq]
  omega

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
AddGroup.ofLeftAxioms (by
  intro a b c
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
  grind
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [show (0 : Int) = 0 —— 0 by rfl]
  simp
) (by
  intro a
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  simp only [neg_eq, add_eq, eq_0']
  omega
)

instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := add_comm

instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

lemma Int.pos_iff_gt_0 {a : Int} : a.IsPos → 0 < a := by
  intro h
  rcases h with ⟨ w, hw ⟩
  constructor
  · use w
    grind
  · by_contra h
    have := cast_eq_0_iff_eq_0 -- grind fails when I remove this
    grind
