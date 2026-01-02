import Mathlib

/-
Definition of a map on the dihedral group determined by parameters k and m.
-/
def dihedralMap {n : ℕ} (k m : ZMod n) : DihedralGroup n → DihedralGroup n
| DihedralGroup.r i => DihedralGroup.r (k * i)
| DihedralGroup.sr i => DihedralGroup.sr (m + k * i)

/-
dihedralMap preserves multiplication.
-/
lemma dihedralMap_mul {n : ℕ} (k m : ZMod n) (x y : DihedralGroup n) :
  dihedralMap k m (x * y) = dihedralMap k m x * dihedralMap k m y := by
    -- Let's consider each case for x and y.
    cases' x with x x <;> cases' y with y y <;> simp +decide [dihedralMap];
    · ring;
    · grind;
    · ring;
    · ring

/-
The map dihedralMap is bijective when k is a unit.
-/
lemma dihedralMap_bijective {n : ℕ} (k : (ZMod n)ˣ) (m : ZMod n) : Function.Bijective (dihedralMap (k : ZMod n) m) := by
  unfold dihedralMap;
  constructor;
  · intro x y; aesop;
  · rintro ⟨ ⟩;
    · use DihedralGroup.r ( k⁻¹ * ‹_› ) ; aesop;
    · rename_i a;
      exact ⟨ DihedralGroup.sr ( k⁻¹ * ( a - m ) ), by simp [ mul_sub ] ⟩

/-
If an element has order n (where n >= 3), it must be a rotation by a unit.
-/
lemma orderOf_eq_n_implies_rotation {n : ℕ} (hn : 3 ≤ n) (x : DihedralGroup n) (hx : orderOf x = n) :
  ∃ k : (ZMod n)ˣ, x = DihedralGroup.r k := by
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ DihedralGroup ];
    -- Since $x$ has order $n + 2$, it must be a rotation by some $k$.
    obtain ⟨k, hk⟩ : ∃ k : ZMod (n + 2), x = DihedralGroup.r k := by
      cases x <;> aesop;
    -- Since $k$ is a unit, we can write $k$ as $k = k' + (n + 2)$ for some $k'$.
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' ∧ Nat.gcd k' (n + 2) = 1 := by
      use k.val;
      have h_unit : orderOf x = (n + 2) / Nat.gcd k.val (n + 2) := by
        rw [ hk, DihedralGroup.orderOf_r ];
        rw [ Nat.gcd_comm ];
      exact ⟨ by erw [ ZMod.natCast_zmod_val ] , by nlinarith [ Nat.div_mul_cancel ( Nat.gcd_dvd_right k.val ( n + 2 ) ) ] ⟩;
    have h_unit : IsUnit (k' : ZMod (n + 2)) := by
      have h_unit : ∃ m : ℕ, k' * m ≡ 1 [MOD (n + 2)] := by
        have := Nat.exists_mul_emod_eq_one_of_coprime hk'.2; aesop;
      exact isUnit_iff_exists_inv.mpr ⟨ h_unit.choose, by simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_unit.choose_spec ⟩;
    obtain ⟨ k, hk ⟩ := h_unit; use k; aesop;

/-
If an element of the dihedral group (n >= 3) has order 2 and is not in the center, it must be a reflection.
-/
lemma isReflection_of_order_two_not_central {n : ℕ} (x : DihedralGroup n) (h2 : orderOf x = 2) (hc : x ∉ Subgroup.center (DihedralGroup n)) : ∃ m : ZMod n, x = DihedralGroup.sr m := by
  -- Since $x$ is not a rotation, it must be a reflection.
  have h_not_rotation : ¬∃ k : ZMod n, x = DihedralGroup.r k := by
    rintro ⟨ k, rfl ⟩;
    refine hc ?_
    rw [ Subgroup.mem_center_iff ];
    rintro ( _ | _ ) <;> simp +decide [ DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r ];
    · ring;
    · have := orderOf_dvd_iff_pow_eq_one.1 ( dvd_of_eq h2 );
      injection this with this ; simp_all +decide [ sub_eq_add_neg ];
      exact eq_neg_of_add_eq_zero_left this;
  cases x <;> aesop

/-
dihedralMap maps 1 to 1.
-/
lemma dihedralMap_one {n : ℕ} (k m : ZMod n) :
  dihedralMap k m 1 = 1 := by
    rcases n with ( _ | _ | n ) <;> norm_cast;
    cases k ; cases m
    · tauto
    · rfl
    · rfl

/-
Definition of the automorphism of the dihedral group corresponding to parameters k and m.
-/
noncomputable def dihedralAut {n : ℕ} (k : (ZMod n)ˣ) (m : ZMod n) : MulAut (DihedralGroup n) :=
  MulEquiv.ofBijective
    ({ toFun := dihedralMap k m,
       map_one' := dihedralMap_one k m,
       map_mul' := dihedralMap_mul k m } : DihedralGroup n →* DihedralGroup n)
    (dihedralMap_bijective k m)

/-
The map from parameters (k, m) to automorphisms is injective.
-/
lemma dihedralAut_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (fun (p : (ZMod n)ˣ × ZMod n) => dihedralAut p.1 p.2) := by
  intros p q h;
  -- By definition of dihedralAut, we know that if two automorphisms are equal, then their corresponding dihedralMap functions must be equal.
  have h_map_eq : dihedralMap p.1 p.2 = dihedralMap q.1 q.2 := by
    exact funext fun x => by simpa using congr_arg ( fun f => f x ) h;
  unfold dihedralMap at h_map_eq;
  have := congr_fun h_map_eq ( DihedralGroup.sr 0 ) ; have := congr_fun h_map_eq ( DihedralGroup.sr 1 ) ; aesop;

/-
An automorphism of the dihedral group is determined by its values on r 1 and sr 0.
-/
lemma aut_determined_by_gens {n : ℕ} (f g : MulAut (DihedralGroup n))
  (h_r : f (DihedralGroup.r 1) = g (DihedralGroup.r 1))
  (h_sr : f (DihedralGroup.sr 0) = g (DihedralGroup.sr 0)) : f = g := by
    -- Since $r 1$ and $sr 0$ generate the entire group, if $f$ and $g$ agree on these generators, they must be equal.
    have h_gen : ∀ x : DihedralGroup n, x ∈ Subgroup.closure ({DihedralGroup.r 1, DihedralGroup.sr 0} : Set (DihedralGroup n)) := by
      intro x
      induction' x using DihedralGroup.rec with k k ih;
      · rcases n with ( _ | _ | n );
        · induction' k using Int.induction_on with n ihn n ihn;
          · exact Subgroup.one_mem _;
          · simpa [ add_comm ] using Subgroup.mul_mem _ ihn ( Subgroup.subset_closure ( Set.mem_insert _ _ ) );
          · simpa [ sub_eq_add_neg ] using Subgroup.mul_mem _ ihn ( Subgroup.inv_mem _ ( Subgroup.subset_closure ( Set.mem_insert _ _ ) ) );
        · fin_cases k ; exact Subgroup.subset_closure ( Set.mem_insert _ _ );
        · convert Subgroup.pow_mem _ ( Subgroup.subset_closure ( Set.mem_insert _ _ ) ) k.val using 1 ; simp +decide [ DihedralGroup.r ];
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Subgroup.mem_closure ];
        · simp_all +decide [ Set.insert_subset_iff ];
          intro K hr hs; induction' k using Int.induction_on with n ihn n ihn; aesop;
          · convert K.mul_mem ihn hr using 1;
          · convert K.mul_mem ihn ( K.inv_mem hr ) using 1;
        · fin_cases k ; simp_all +decide [ Set.insert_subset_iff ];
        · intro K hK; have := hK ( Set.mem_insert _ _ ) ; have := hK ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ; simp_all +decide [ Set.insert_subset_iff ] ;
          convert K.mul_mem this ( K.pow_mem ‹DihedralGroup.r 1 ∈ K› k.val ) using 1 ; aesop;
    refine' MulEquiv.ext fun x => _;
    induction h_gen x using Subgroup.closure_induction ; aesop;
    · simp +decide;
    · aesop;
    · aesop

/-
For n >= 3, the reflection sr 0 is not in the center of the dihedral group.
-/
lemma sr_not_central {n : ℕ} (hn : 3 ≤ n) : DihedralGroup.sr 0 ∉ Subgroup.center (DihedralGroup n) := by
  simp +decide [ Subgroup.mem_center_iff ];
  refine' ⟨ DihedralGroup.r 1, _ ⟩ ; simp +decide [ DihedralGroup.r ];
  rcases n with ( _ | _ | _ | n ) <;> norm_num [ Fin.ext_iff ] at *;
  rw [ neg_eq_iff_add_eq_zero ] ; norm_num;
  rintro ⟨ ⟩

/-
The map from parameters (k, m) to automorphisms is surjective.
-/
lemma dihedralAut_surjective {n : ℕ} (hn : 3 ≤ n) : Function.Surjective (fun (p : (ZMod n)ˣ × ZMod n) => dihedralAut p.1 p.2) := by
  -- Let's choose any automorphism $f$ of the dihedral group.
  intro f
  -- By definition of automorphism, $f$ must map $r 1$ to some element of order $n$ and $sr 0$ to some element of order $2$.
  obtain ⟨k, hk⟩ : ∃ k : (ZMod n)ˣ, f (DihedralGroup.r 1) = DihedralGroup.r k := by
    have h_order : orderOf (f (DihedralGroup.r 1)) = n := by
      simp +decide [ orderOf_eq_iff ];
    have := orderOf_eq_n_implies_rotation hn ( f ( DihedralGroup.r 1 ) ) h_order; aesop;
  obtain ⟨m, hm⟩ : ∃ m : ZMod n, f (DihedralGroup.sr 0) = DihedralGroup.sr m := by
    -- Since $f$ is an automorphism, $f(sr_0)$ must be a reflection.
    have h_sr : f (DihedralGroup.sr 0) ∈ {x : DihedralGroup n | ¬x ∈ Subgroup.center (DihedralGroup n)} := by
      -- Since $f$ is an automorphism, it preserves the property of being in the center.
      have h_center_preserved : ∀ x : DihedralGroup n, x ∈ Subgroup.center (DihedralGroup n) ↔ f x ∈ Subgroup.center (DihedralGroup n) := by
        simp +decide [ Subgroup.mem_center_iff ];
        intro x; constructor <;> intro h g <;> have := h ( f.symm g ) <;> simp_all +decide ;
        · simpa using congr_arg f ( h ( f.symm g ) );
        · have := f.surjective g; obtain ⟨ y, rfl ⟩ := this; have := h y; simp_all +decide [ mul_assoc ] ;
          have := f.injective; have := h ( f y ) ; aesop;
      exact fun h => sr_not_central hn <| h_center_preserved _ |>.2 h;
    have h_order : orderOf (f (DihedralGroup.sr 0)) = 2 := by
      simp +decide [ orderOf_eq_iff ];
    exact?;
  refine' ⟨ ⟨ k, m ⟩, _ ⟩;
  -- By definition of $dihedralAut$, we know that $dihedralAut k m (r 1) = r k$ and $dihedralAut k m (sr 0) = sr m$.
  have h_dihedralAut_r : dihedralAut k m (DihedralGroup.r 1) = DihedralGroup.r k := by
    simp +decide [ dihedralAut ];
    simp +decide [ dihedralMap ]
  have h_dihedralAut_sr : dihedralAut k m (DihedralGroup.sr 0) = DihedralGroup.sr m := by
    exact show dihedralMap k m ( DihedralGroup.sr 0 ) = DihedralGroup.sr m from by unfold dihedralMap; aesop;
  exact aut_determined_by_gens _ _ ( h_dihedralAut_r.trans hk.symm ) ( h_dihedralAut_sr.trans hm.symm )

example {n : ℕ} (hn : 6 ≤ n)
: Nat.card (MulAut (DihedralGroup n)) = n * Nat.totient n := by
  have h_card : Nat.card (MulAut (DihedralGroup n)) = Nat.card ((ZMod n)ˣ × ZMod n) := by
    apply Nat.card_congr;
    exact Equiv.symm <| Equiv.ofBijective _ ⟨ dihedralAut_injective <| by linarith, dihedralAut_surjective <| by linarith ⟩;
  cases n <;> simp_all +decide [ Nat.totient ];
  ring
