import Mathlib

lemma either_r_or_sr
  (n : ℕ)
  (x : DihedralGroup n)
: (∃ i, x = DihedralGroup.r i) ∨ (∃ j, x = DihedralGroup.sr j) := by
  match x with
  | DihedralGroup.r i => tauto
  | DihedralGroup.sr j => tauto


example
  (n : ℕ)
  (x : DihedralGroup n)
  (hx : ¬ (∃ i, x = DihedralGroup.r i)) -- x is not a power of r
: (DihedralGroup.r 1) * x = x * (DihedralGroup.r (-1)) := by
  have : ∃ j, x = DihedralGroup.sr j := by
    have := either_r_or_sr n x
    grind
  obtain ⟨j, rfl⟩ := this
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  simp
  ring

-- 1.7.1
example {F : Type*} [Field F] : MulAction Fˣ F := {
  smul := fun x y ↦ x * y
  one_smul := by
    intro x
    simp
  mul_smul := by
    rintro x y z
    rw [show (x * y) • z = (x * y) * z by rfl]
    rw [show y • z = y * z by rfl]
    rw [show x • (y * z) = x * (y * z) by rfl]
    rw [mul_assoc]
}

example {F : Type*} [Field F] : MulAction F F := {
  smul := fun x y ↦ x * y
  one_smul := by
    intro x
    simp
  mul_smul := by
    rintro x y z
    simp [mul_assoc]
}

-- 1.7.4a
def action_kernel {G B} [Group G] (σ : MulAction G B) : Subgroup G := {
  carrier := { g : G | ∀ b : B, g • b = b}
  mul_mem' := by
    rintro a b ha hb
    simp at *
    intro c
    rw [σ.mul_smul, ha, hb]
  one_mem' := by
    simp [σ.one_smul]
  inv_mem' := by
    intro x hx
    simp at *
    intro b
    have : (1 : G) • b = x • b := by simp [hx]
    rw [show (1 : G) = x * x⁻¹ by group, σ.mul_smul, hx, hx] at this
    exact this
}

-- example
def MyTrivialAction (G : Type u) : Type u := G

instance  {G} [Group G] : Group (MyTrivialAction G) := ‹Group G›

def ofTrivialAction {G : Type*} [Group G] : MyTrivialAction G ≃* G where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

lemma ofTrivialAction_eq {G : Type*} [Group G] (g : MyTrivialAction G) : ofTrivialAction g = g := rfl

def toTrivialAction {G : Type*} [Group G] : G ≃* MyTrivialAction G :=
  MulEquiv.symm ofTrivialAction

instance {G} [Group G] : SMul (MyTrivialAction G) G where
  smul := fun _ h ↦ h

lemma smul_eq'' {G : Type*} [Group G] (g : MyTrivialAction G) (h : G) : g • h =  h := rfl

-- example
instance {G} [Group G] : MulAction (MyTrivialAction G) G := {
  one_smul b := by simp [smul_eq'']
  mul_smul x y b := by simp [smul_eq'']
}


-- 1.7.3
def MyEx3Action := ℝ

instance : AddGroup (MyEx3Action) := Real.instAddGroup

def ofEx3Action : MyEx3Action ≃+ ℝ where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl

lemma ofEx3Action_eq (g : MyEx3Action) : ofEx3Action g = g := rfl

def toEx3Action : ℝ ≃+ MyEx3Action :=
  AddEquiv.symm ofEx3Action

instance : VAdd (MyEx3Action) (ℝ × ℝ) where
  vadd := fun r (x, y) ↦ (x + (ofEx3Action r) * y, y)

lemma vadd_eq (r : MyEx3Action) (p : ℝ × ℝ): r +ᵥ p = (p.fst + (ofEx3Action r) * p.snd, p.snd) := by
  rfl

-- 1.7.3
instance : AddAction (MyEx3Action) (ℝ × ℝ) := {
  zero_vadd p := by
    simp [vadd_eq]
  add_vadd r p q := by
    simp [vadd_eq]
    ring
}

-- 1.7.15
def MyRightMulAction (G : Type u) : Type u := G

instance  {G} [Group G] : Group (MyRightMulAction G) := ‹Group G›

def ofRightMulAction {G : Type*} [Group G] : MyRightMulAction G ≃* G where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

lemma ofRightMulAction_eq {G : Type*} [Group G] (g : MyRightMulAction G) : ofRightMulAction g = g := rfl

def toRightMulAction {G : Type*} [Group G] : G ≃* MyRightMulAction G :=
  MulEquiv.symm ofRightMulAction

instance {G} [Group G] : SMul (MyRightMulAction G) G where
  smul := fun g h ↦ h * (ofRightMulAction g)⁻¹

lemma smul_eq' {G : Type*} [Group G] (g : MyRightMulAction G) (h : G) : g • h =  h * (ofRightMulAction g)⁻¹ := rfl

-- 1.7.15
instance {G} [Group G] : MulAction (MyRightMulAction G) G := {
  one_smul b := by
    simp [smul_eq']
  mul_smul x y b := by
    simp [smul_eq', ofRightMulAction_eq]
    group
}

-- 1.7.16
def MyConjAct (G : Type u) : Type u := G

instance  {G} [Group G] : Group (MyConjAct G) := ‹Group G›

def ofConjAct {G : Type*} [Group G] : MyConjAct G ≃* G where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

lemma ofConjAct_eq {G : Type*} [Group G] (g : MyConjAct G) : ofConjAct g = g := rfl

def toConjAct {G : Type*} [Group G] : G ≃* MyConjAct G :=
  MulEquiv.symm ofConjAct

instance [Group G] : SMul (MyConjAct G) G where smul g h := ofConjAct g * h * (ofConjAct g)⁻¹

lemma smul_eq {G : Type*} [Group G] (g : MyConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ := rfl

-- 1.7.16
instance {G} [Group G] : MulAction (MyConjAct G) G := {
  one_smul b := by
    simp [smul_eq]
  mul_smul x y b := by
    simp [smul_eq, ofConjAct_eq]
    group
}

-- 1.7.17 part 1
def conjIsomorphism {G} [Group G] (g : MyConjAct G) : G ≃* G := {
  toFun := fun x ↦ g • x
  invFun := fun x ↦ g⁻¹ • x
  left_inv := by
    intro x
    simp [smul_eq']
  right_inv := by
    intro x
    simp [smul_eq']
  map_mul' := by
    intro x y
    simp [smul_eq, ofRightMulAction_eq]
}

-- 1.7.17 part 2
example {G} [Group G] (g : G) (x : G): orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (conjIsomorphism g) x
  simpa [conjIsomorphism, smul_eq, ofConjAct_eq]

-- 1.7.8
structure kElementSubsets (A : Type*) (k : ℕ) where
  elems: Set A
  card_eq_k: Nat.card elems = k

instance {A : Type*} (k : ℕ) : SMul (Equiv.Perm A) (kElementSubsets A k) := {
  smul σ s := {
    elems := σ '' s.elems,
    card_eq_k := by
      have h_card := Nat.card_image_of_injective σ.injective s.elems
      rw [s.card_eq_k] at h_card
      exact h_card
  }
}

lemma smul_eq_ {A : Type*} (k : ℕ) (σ : Equiv.Perm A) (s : kElementSubsets A k) : σ • s = {
  elems := σ '' s.elems,
  card_eq_k := by
    have h_card := Nat.card_image_of_injective σ.injective s.elems
    rw [s.card_eq_k] at h_card
    exact h_card
} := by rfl


-- 1.7.8
-- Let A be a nonempty set and let k be a positive integer with k ≤ |A|. The symmetric group S_A acts on the set of all subsets of A of cardinality k.
def k1 (A : Type*) (k : ℕ) : MulAction (Equiv.Perm A) (kElementSubsets A k) := {
  one_smul b := by
    simp [smul_eq_]
  mul_smul x y b := by
    simp only [smul_eq_, Set.image_comp]
    dsimp
    rw [kElementSubsets.mk.injEq]
    rw [Set.image_comp]
}

example {A} (f : A → A) (g : A → A) (s : Set A)
: (f ∘ g) '' s = f '' (g '' s) := Set.image_comp f g s

-- 1.7.9
structure kElementLists (A : Type*) (k : ℕ) where
  elems: List A
  card_eq_k: elems.length = k

instance {A : Type*} (k : ℕ) : SMul (Equiv.Perm A) (kElementLists A k) := {
  smul σ s := {
    elems := s.elems.map σ,
    card_eq_k := by
      simp only [List.length_map, s.card_eq_k]
  }
}

lemma smul_eq_' {A : Type*} (k : ℕ) (σ : Equiv.Perm A) (s : kElementLists A k) : σ • s = {
  elems := s.elems.map σ,
  card_eq_k := by
    simp only [List.length_map, s.card_eq_k]
} := by rfl

-- 1.7.9
def k2 (A : Type*) (k : ℕ) : MulAction (Equiv.Perm A) (kElementLists A k) := {
  one_smul b := by
    simp [smul_eq_']
  mul_smul x y b := by
    simp only [smul_eq_', Equiv.Perm.coe_mul, List.map_map]
}

def IsFaithful {G A: Type*} [Group G] (σ : MulAction G A) : Prop := ∀ g₁ g₂ : G, ∀ a : A, g₁ • a = g₂ • a → g₁ = g₂

#eval permsOfFinset (⊤ : Finset (Fin 4))

#check (1 : Equiv.Perm (Fin 4))
#check (c[2, 3, 0, 1] : Equiv.Perm (Fin 4))

-- 1.7.10 partial results

#check k2

#eval List.map ((Equiv.swap 0 1) ∘ (Equiv.swap 2 3)) {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}


example : (fun x ↦ x + 1) '' { 1, 2, 3} = { 2, 3, 4} := by
  ext y
  simp [Set.mem_image, eq_comm]

example : ¬ IsFaithful (k1 (Fin 4) 4) := by
  simp [IsFaithful]
  use 1
  use Equiv.swap 0 1
  simp
  constructor
  · use { elems := {0, 1, 2, 3}, card_eq_k := by simp }
    simp [smul_eq_]
    ext x
    simp [Set.mem_image, eq_comm]
    decide +revert
  decide +revert

def IsSameOrbit {H A} [Group H] (σ : MulAction H A) : A → A → Prop := fun a b ↦ ∃ h : H, h • a = b

def IsSameOrbitEquivalence {H A} [Group H] (σ : MulAction H A) : Equivalence (IsSameOrbit σ) := {
  refl a := by
    unfold IsSameOrbit
    use 1
    simp
  symm := by
    rintro a b ⟨h, rfl⟩
    use h⁻¹
    simp
  trans := by
    rintro a b c ⟨h, rfl⟩ ⟨k, rfl⟩
    use k * h
    simp [σ.mul_smul]
}

def MySetoid {H A} [Group H] (σ : MulAction H A) : Setoid A := {
  r a b := IsSameOrbit σ a b
  iseqv := IsSameOrbitEquivalence σ
}

def orbit {H A} [Group H] (σ : MulAction H A) (a : A) : Set A := { b | IsSameOrbit σ a b }

def myMap {G} [Group G] (H : Subgroup G) (x : G): H ≃ (orbit (Subgroup.instMulAction : MulAction H G) x) := {
  toFun := fun h ↦ ⟨ h • x, by
    use h
  ⟩
  invFun := fun ⟨hx, p⟩ ↦ ⟨hx * x⁻¹, by
    unfold orbit at p
    simp at p
    unfold IsSameOrbit at p
    obtain ⟨h, rfl⟩ := p
    rw [show h • x = h * x by rfl]
    simp
  ⟩
  left_inv h := by
    simp [MulAction.mul_smul, Subgroup.smul_def]
  right_inv _ := by
    simp only [Subgroup.mk_smul, smul_eq_mul, inv_mul_cancel_right]
}

example {X} (s : Set X) (h : Nat.card s = 3) : ∃ s' : Finset X, s = s' := by
  have h_finite : Set.Finite s := by
    apply Nat.finite_of_card_ne_zero; exact h.symm ▸ by decide;
  generalize_proofs at *;
  use h_finite.toFinset;
  simp

-- Lagrange's Theorem
example {G} [Group G] [DecidableEq G] [Fintype G] (H : Subgroup G) : ∃ n, Fintype.card G = n * Nat.card H := by
  have {S} (s : Setoid S) : DecidableRel s.r := Classical.decRel ⇑s
  let myAction : MulAction H G:= Subgroup.instMulAction
  let mySetoid := MySetoid myAction
  let myFP := Finpartition.ofSetoid mySetoid

  have : ∀ t ∈ myFP.parts, Finset.card t = Nat.card H := by
    intro t ht
    unfold myFP at ht
    unfold Finpartition.ofSetoid at ht
    rw [Finpartition.ofSetSetoid_parts] at ht
    simp at ht
    obtain ⟨a, rfl⟩ := ht
    unfold mySetoid MySetoid
    simp

    have rwt : { b | IsSameOrbit myAction a b }  = orbit myAction a := rfl
    have h_bij : Nonempty (↥H ≃ {b : G | IsSameOrbit myAction a b}) := by
      exact ⟨ Equiv.ofBijective ( fun g => ⟨ g • a, by
        use g ⟩ ) ⟨ by
        intro g₁ g₂ h; aesop, by
        intro ⟨ b, hb ⟩ ; cases' hb with g hg ; use ⟨ g, by
          aesop ⟩ ; aesop
        ⟩ ⟩;
    have h_card_eq : Nat.card H = Nat.card {b : G | IsSameOrbit myAction a b} := by
      exact Nat.card_congr h_bij.some;
    rw [ ← Nat.card_eq_finsetCard ] ; aesop;
  have h_sum : ∑ t ∈ myFP.parts, t.card = Fintype.card G := by
    convert myFP.sum_card_parts;
  have h_card_parts : ∑ t ∈ myFP.parts, t.card = (Finset.card myFP.parts) * Nat.card H := by
    rw [ Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul ];
    simp [Nat.cast_id];
  exact ⟨ _, h_sum.symm.trans h_card_parts ⟩
