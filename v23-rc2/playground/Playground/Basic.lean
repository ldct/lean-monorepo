namespace Section_4_1

structure PreInt where
  minuend : Nat
  subtrahend : Nat

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro ⟨a, b⟩
      grind
    symm := by
      intro ⟨a, b⟩ ⟨c, d⟩ h
      grind
    trans := by
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      grind
    }

@[simp]
theorem PreInt.equiv (a b c d : Nat) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b : Nat) : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

theorem Int.eq (a b c d : Nat) : formalDiff a b = formalDiff c d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

instance Int.instOfNat {n : Nat} : OfNat Int n where
  ofNat := formalDiff n 0

instance Int.instNatCast : NatCast Int where
  natCast n := formalDiff n 0

theorem Int.natCast_eq (n : Nat) : (n : Int) = formalDiff n 0 := rfl

theorem Int.natCast_inj (n m : Nat) :
  (n : Int) = (m : Int) ↔ n = m := by
  rw [natCast_eq, natCast_eq, eq]
  grind

@[grind]
theorem Int.eq_0_of_cast_eq_0 (n : Nat) (h : (n : Int) = 0) : n = 0 := by
  rw [show (0 : Int) = ((0 : Nat) : Int) by rfl] at h
  rwa [natCast_inj] at h

theorem Int.pos_iff_gt_0 {a : Int} : (∃ (n:Nat), n > 0 ∧ a = n) → a ≠ 0 := by
  intro ⟨ w, hw ⟩ h
  have := eq_0_of_cast_eq_0 -- grind fails when I remove this
  grind

end Section_4_1
