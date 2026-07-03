import Mathlib


namespace DihedralAsProduct

abbrev DihedralProduct (n : ℕ) : Type :=
  Multiplicative (ZMod 2) × DihedralGroup n

example : Nonempty
  ((DihedralGroup 6) ≃* (DihedralProduct 3)) := by
  constructor;
  symm;
  refine' { Equiv.ofBijective ( fun x => _ ) ⟨ _, _ ⟩ with .. };
  exact if x.1 = Multiplicative.ofAdd 0 then if x.2 = DihedralGroup.r 0 then DihedralGroup.r 0 else if x.2 = DihedralGroup.r 1 then DihedralGroup.r 2 else if x.2 = DihedralGroup.r 2 then DihedralGroup.r 4 else if x.2 = DihedralGroup.sr 0 then DihedralGroup.sr 0 else if x.2 = DihedralGroup.sr 1 then DihedralGroup.sr 2 else DihedralGroup.sr 4 else if x.2 = DihedralGroup.r 0 then DihedralGroup.r 3 else if x.2 = DihedralGroup.r 1 then DihedralGroup.r 5 else if x.2 = DihedralGroup.r 2 then DihedralGroup.r 1 else if x.2 = DihedralGroup.sr 0 then DihedralGroup.sr 3 else if x.2 = DihedralGroup.sr 1 then DihedralGroup.sr 5 else DihedralGroup.sr 1;
  all_goals simp +decide [ Function.Injective, Function.Surjective ]

noncomputable section AristotleLemmas

/-
Construct an isomorphism between D_{2m} and C_2 x D_m when m is odd.
-/
def dihedralIsoOdd (m : ℕ) (hm : m % 2 = 1) :
  DihedralGroup (2 * m) ≃* DihedralProduct m := by
  have h_coprime : Nat.Coprime 2 m := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    exact hm
  let crt := ZMod.chineseRemainder h_coprime
  apply MulEquiv.mk
    (Equiv.mk
      (fun g => match g with
        | DihedralGroup.r i => (Multiplicative.ofAdd (crt i).1, DihedralGroup.r (crt i).2)
        | DihedralGroup.sr i => (Multiplicative.ofAdd (crt i).1, DihedralGroup.sr (crt i).2))
      (fun p => match p with
        | (x, DihedralGroup.r j) => DihedralGroup.r (crt.symm (x.toAdd, j))
        | (x, DihedralGroup.sr j) => DihedralGroup.sr (crt.symm (x.toAdd, j)))
      (by intro g; cases g <;> simp [crt.symm_apply_apply])
      (by rintro ⟨x, y⟩; cases y <;> simp [crt.apply_symm_apply]))
    (by
      intro g h
      cases g <;> cases h <;> simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, Prod.mk_mul_mk, Mul.mul]
      ·
        aesop
      ·
        -- Since we're working in ZMod 2, subtraction is the same as addition. Therefore, (crt (a - b)).1 = (crt a).1 + (crt b).1.
        have h_sub : ∀ a b : ZMod (2 * m), (crt (a - b)).1 = (crt a).1 + (crt b).1 := by
          simp +decide [ sub_eq_add_neg ];
        simp_all +decide [ add_comm, mul_comm ]
      ·
        aesop
      ·
        -- By definition of multiplication in the dihedral group, we have:
        simp [DihedralGroup.r_mul_r];
        -- Since we're working in ZMod 2, the multiplicative group is just {1, -1}. So, if the elements are 1 or -1, their product should be the same as their division.
        have h_cases : ∀ x y : ZMod 2, Multiplicative.ofAdd x / Multiplicative.ofAdd y = Multiplicative.ofAdd y * Multiplicative.ofAdd x := by
          native_decide +revert;
        exact h_cases _ _)

end AristotleLemmas

example {n : ℕ} (hn1 : 6 ≤ n) (hn2 : ∃ k, n = 4 * k + 2): Nonempty
  ((DihedralGroup n) ≃* (DihedralProduct (n/2))) := by
  refine' ⟨ _ ⟩;
  have h_iso : DihedralGroup (2 * (n / 2)) ≃* DihedralProduct (n / 2) := by
    apply dihedralIsoOdd;
    omega;
  convert h_iso using 1 ; rw [ Nat.mul_div_cancel' ] ; omega;
  grind


end DihedralAsProduct