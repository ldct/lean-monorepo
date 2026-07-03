import Playground.Borcherds.Part1

namespace Borcherds

/- Section 1.2 -/

@[ext]
structure TrivialGroup : Type where
  val : Unit

instance : One TrivialGroup where one := {val := Unit.unit}
instance : Mul TrivialGroup where mul _ _ := {val := Unit.unit}
instance : Inv TrivialGroup where inv _ := {val := Unit.unit}

instance : Group TrivialGroup where
  mul_assoc a b c := by ext
  one_mul a := by ext
  mul_one a := by ext
  inv_mul_cancel a := by ext
  mul_inv_cancel a := by ext

/- The `Equiv` between any group of order 1 and the trivial group -/
def trivialEquiv {G} [Group G] (h : Nat.card G = 1) : G ≃ TrivialGroup where
  toFun _ := ⟨()⟩
  invFun _ := 1
  left_inv x := by
    have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
    exact Subsingleton.elim _ _
  right_inv x := by ext

/- Classification of groups of order 1, proposition 1.3 -/

/- The isomorphism between any group of order 1 and the trivial group -/
def trivialIso {G} [Group G] [Fintype G] (h : Nat.card G = 1) : GroupIso G TrivialGroup where
  toEquiv := trivialEquiv h
  map_mul x y := by ext
  map_one := by ext
  map_inv x := by ext

/- Definition 1.3 - Subgroups-/
structure BSubgroup (G : Type*) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  inv_mem : ∀ x : G, x ∈ carrier → x⁻¹ ∈ carrier

instance {G : Type*} [Group G] : CoeSort (BSubgroup G) (Type _) where
  coe H := { x : G // x ∈ H.carrier }


/- The group structure on the coercion of a subgroup to a type -/
instance {G : Type*} [Group G] (H : BSubgroup G) : Group H where
  mul := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, H.mul_mem a b ha hb⟩
  one := ⟨1, H.one_mem⟩
  inv := fun ⟨a, ha⟩ => ⟨a⁻¹, H.inv_mem a ha⟩
  mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Subtype.ext (Group.mul_assoc a b c)
  one_mul := fun ⟨a, _⟩ => Subtype.ext (Group.one_mul a)
  mul_one := fun ⟨a, _⟩ => Subtype.ext (Group.mul_one a)
  inv_mul_cancel := fun ⟨a, _⟩ => Subtype.ext (Group.inv_mul_cancel a)
  mul_inv_cancel := fun ⟨a, _⟩ => Subtype.ext (Group.mul_inv_cancel a)

/-
g • S ≃ S as sets
-/
open scoped Pointwise in
example {G} [_root_.Group G] (g : G) (S : Set G) : (g • S : Set G) ≃ S where
  toFun := fun x => ⟨g⁻¹ * x.1, by
    obtain ⟨s, hs, hgs⟩ := x.2
    simp only [← hgs, smul_eq_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hs⟩
  invFun := fun x => ⟨g * x.1, Set.smul_mem_smul_set x.2⟩
  left_inv := fun x => by ext; simp
  right_inv := fun x => by ext; simp

def SameLeftCoset {G} [Group G] (H : BSubgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H.carrier
  iseqv := {
    refl g := by
      simp [H.one_mem]
    symm := by
      intro a b h
      have := H.inv_mem _ h
      rw [Borcherds.Group.mul_inv] at this
      rwa [Borcherds.Group.inv_inv] at this
    trans := by
      intro a b c h1 h2
      have := H.mul_mem _ _ h1 h2
      rw [← Borcherds.Group.mul_assoc] at this
      rw [show a⁻¹ * b * b⁻¹ = a⁻¹ * (b * b⁻¹) by apply
        Borcherds.Group.mul_assoc] at this
      simp only [Borcherds.Group.mul_inv_cancel, Borcherds.Group.mul_one] at this
      exact this
    }

/- The quotient of a group by a subgroup is the quotient of the setoid on G where two elements are related if they are in the same left coset of the subgroup. -/
instance {G} [Borcherds.Group G] : HasQuotient G (BSubgroup G) where
  Quotient H := Quotient (SameLeftCoset H)

section Lagrange

variable {G : Type*} [Borcherds.Group G] (H : BSubgroup G) (g : G)

open scoped Pointwise in
/-- For `g : G`, left multiplication identifies `H` with the left coset `g • H`. -/
def BSubgroup.leftCosetEquiv' (g : G) :
      H.carrier ≃
      (g • H.carrier : Set G)
  where
  toFun := fun ⟨h, hh⟩ => ⟨g * h, ⟨h, hh, rfl⟩⟩
  invFun := fun ⟨x, hx⟩ =>
    ⟨g⁻¹ * x, by
      obtain ⟨s, hs, hgs⟩ := hx
      have : g⁻¹ * x = s := by
        rw [← hgs]
        change g⁻¹ * (g * s) = s
        rw [← Borcherds.Group.mul_assoc, Borcherds.Group.inv_mul_cancel,
            Borcherds.Group.one_mul]
      rw [this]
      exact hs⟩
  left_inv := fun ⟨h, _⟩ => Subtype.ext (by
    change g⁻¹ * (g * h) = h
    rw [← Borcherds.Group.mul_assoc, Borcherds.Group.inv_mul_cancel,
        Borcherds.Group.one_mul])
  right_inv := fun ⟨x, _⟩ => Subtype.ext (by
    change g * (g⁻¹ * x) = x
    rw [← Borcherds.Group.mul_assoc, Borcherds.Group.mul_inv_cancel,
        Borcherds.Group.one_mul])

open scoped Pointwise in
/-- Being in the same left coset is equivalent to
    membership in the pointwise smul set `g • H.carrier`. -/
lemma BSubgroup.quotient_eq_iff_mem_smul (g x : G) :
    (⟦x⟧ : G ⧸ H) = ⟦g⟧ ↔ x ∈ g • H.carrier where
  mp hx := by
    have hmem : x⁻¹ * g ∈ H.carrier := Quotient.exact hx
    refine ⟨g⁻¹ * x, ?_, ?_⟩
    · have heq : g⁻¹ * x = (x⁻¹ * g)⁻¹ := by
        rw [Borcherds.Group.mul_inv, Borcherds.Group.inv_inv]
      rw [heq]
      exact H.inv_mem _ hmem
    · change g * (g⁻¹ * x) = x
      rw [← Borcherds.Group.mul_assoc, Borcherds.Group.mul_inv_cancel,
          Borcherds.Group.one_mul]
  mpr := by
    rintro ⟨s, hs, hgs⟩
    have hxeq : x = g * s := hgs.symm
    apply Quotient.sound
    change x⁻¹ * g ∈ H.carrier
    rw [hxeq]
    have heq : (g * s)⁻¹ * g = s⁻¹ := by
      rw [Borcherds.Group.mul_inv, Borcherds.Group.mul_assoc,
          Borcherds.Group.inv_mul_cancel, Borcherds.Group.mul_one]
    rw [heq]
    exact H.inv_mem _ hs

open scoped Pointwise in
/-- `G` splits non-canonically as the product of coset space and subgroup carrier. -/
noncomputable def BSubgroup.groupEquivQuotientProdSubtype :
    G ≃ (G ⧸ H) × { x // x ∈ H.carrier } := by
  calc G
    -- Step 1: partition G into fibers of the quotient map
      ≃ Σ C : G ⧸ H, { x // ⟦x⟧ = C } :=
        (Equiv.sigmaFiberEquiv (Quotient.mk (SameLeftCoset H))).symm
    -- Step 2: identify each fiber with the left coset `(Quotient.out C) • H.carrier`
    _ ≃ Σ C : G ⧸ H, (Quotient.out C • H.carrier : Set G) := by
        apply Equiv.sigmaCongrRight; intro C
        apply Equiv.subtypeEquivRight; intro x
        rw [← H.quotient_eq_iff_mem_smul, Quotient.out_eq]
    -- Step 3: each coset `g • H.carrier ≃ H.carrier` via leftCosetEquiv'
    _ ≃ Σ C : G ⧸ H, H.carrier := by
        apply Equiv.sigmaCongrRight; intro C
        exact (H.leftCosetEquiv' (Quotient.out C)).symm
    -- Step 4: Σ over a constant fiber ≃ product
    _ ≃ (G ⧸ H) × { x // x ∈ H.carrier } := Equiv.sigmaEquivProd _ _

/-- **Lagrange:** `|G| = |G/H| · |H|` for finite `G` (with `|H|` meant as `Nat.card` of the carrier subtype). -/
theorem BSubgroup.card_eq_card_quotient_mul_card_carrier [Finite G] :
    Nat.card G = Nat.card (G ⧸ H) * Nat.card { x // x ∈ H.carrier } := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  rw [← Nat.card_prod]
  exact Nat.card_congr (BSubgroup.groupEquivQuotientProdSubtype H)

theorem BSubgroup.card_carrier_dvd_card [Finite G] :
  Set.ncard H.carrier ∣ Nat.card G := by
  rw [BSubgroup.card_eq_card_quotient_mul_card_carrier H]
  exact dvd_mul_left _ _

end Lagrange

/-- Integers mod `n`, written multiplicatively (so the group law is addition in `ZMod n`). -/
@[ext]
structure CyclicGroup (n : ℕ) where
  val : ZMod n
deriving DecidableEq

instance (n : ℕ) : Mul (CyclicGroup n) where
  mul a b := ⟨(a.val + b.val)⟩

instance (n : ℕ) : One (CyclicGroup n) where
  one := ⟨0⟩

instance (n : ℕ) : Inv (CyclicGroup n) where
  inv a := ⟨-a.val⟩

@[simp] lemma CyclicGroup.mul_val {n : ℕ} (a b : CyclicGroup n) : (a * b).val = a.val + b.val :=
  rfl

@[simp] lemma CyclicGroup.one_val (n : ℕ) : (1 : CyclicGroup n).val = 0 :=
  rfl

@[simp] lemma CyclicGroup.inv_val {n : ℕ} (a : CyclicGroup n) : (a⁻¹).val = -a.val :=
  rfl

instance (n : ℕ) : Borcherds.Group (CyclicGroup n) where
  mul_assoc a b c := by ext; simp [add_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

@[simp] lemma CyclicGroup.mk_zero_eq_one (n : ℕ) : (⟨0⟩ : CyclicGroup n) = 1 := rfl

/- Classification of groups of order 2 -/

/- The isomorphism between any group of order 2 and the cyclic group of order 2 -/
noncomputable def orderTwoIso {G} [Borcherds.Group G] [Fintype G] (h : Nat.card G = 2) :
    Borcherds.GroupIso G (CyclicGroup 2) := by
  classical
  rw [Nat.card_eq_fintype_card] at h
  have hne : ∃ g : G, g ≠ 1 := by
    by_contra hall; push Not at hall
    have : Fintype.card G ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro a b; rw [hall a, hall b]
    omega
  let g : G := Classical.choose hne
  have hg : g ≠ 1 := Classical.choose_spec hne
  -- Every element is 1 or g
  have helem : ∀ x : G, x = 1 ∨ x = g := by
    have huniv : ({1, g} : Finset G) = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hg), Finset.card_singleton, h])
    intro x; simpa [← huniv] using Finset.mem_univ x
  -- g * g = 1 (it can't be g, by cancellation that would give g = 1)
  have hgg : g * g = 1 := by
    rcases helem (g * g) with h | h
    · exact h
    · exfalso; exact hg (Borcherds.Group.left_cancel g g 1 (by simp [h]))
  -- g is its own inverse
  have hginv : g⁻¹ = g := by
    exact ((Borcherds.Group.mul_eq_one_iff_right g g).mp hgg).symm
  -- Build the isomorphism: 1 ↦ ⟨0⟩, g ↦ ⟨1⟩
  exact {
    toEquiv := {
      toFun := fun x => if x = 1 then ⟨0⟩ else ⟨1⟩
      invFun := fun y => if y.val = 0 then 1 else g
      left_inv x := by grind [helem x]
      right_inv := by
        have key : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
        rintro ⟨y⟩
        rw [CyclicGroup.ext_iff]
        rcases key y with rfl | rfl <;> simp [hg, CyclicGroup.one_val]
    }
    map_mul := by
      intro x y
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl <;> rcases helem y with rfl | rfl <;>
        simp only [hg, hgg, Borcherds.Group.one_mul, Borcherds.Group.mul_one] <;>
        ext <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl]
    map_one := by simp only [Equiv.coe_fn_mk, if_true]; rfl
    map_inv := by
      intro x
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl
      <;> simp [hginv, CyclicGroup.inv_val, CyclicGroup.ext_iff]
  }

/- Classification of groups of order 3 -/

noncomputable def orderThreeIso {G} [Borcherds.Group G] [Fintype G] (h : Nat.card G = 3) :
    Borcherds.GroupIso G (CyclicGroup 3) := by
  classical
  have hcard : Fintype.card G = 3 := by rwa [Nat.card_eq_fintype_card] at h
  -- Pick a non-identity element g
  have hne : ∃ g : G, g ≠ 1 := Fintype.exists_ne_of_one_lt_card (by omega) 1
  let g : G := Classical.choose hne
  have hg : g ≠ 1 := Classical.choose_spec hne
  -- g² ≠ 1 (otherwise {1, g} is a subgroup of order 2, but 2 ∤ 3)
  have hg2 : g * g ≠ 1 := by
    intro hgg
    have hinv : g⁻¹ = g := ((Borcherds.Group.mul_eq_one_iff_right g g).mp hgg).symm
    let H : BSubgroup G := {
      carrier := {1, g}
      one_mem := by simp
      mul_mem := by rintro x y (rfl | rfl) (rfl | rfl) <;> simp [hgg]
      inv_mem := by rintro x (rfl | rfl) <;> simp [hinv, Borcherds.Group.one_inv]
    }
    have hdvd := H.card_carrier_dvd_card
    rw [show H.carrier = ({1, g} : Set G) from rfl, Set.ncard_pair (Ne.symm hg), h] at hdvd
    omega
  -- g² ≠ g (by cancellation that would give g = 1)
  have hg2g : g * g ≠ g := fun heq => hg (Borcherds.Group.left_cancel g g 1 (by simp [heq]))
  -- Every element is 1, g, or g²
  have helem : ∀ x : G, x = 1 ∨ x = g ∨ x = g * g := by
    have huniv : ({1, g, g * g} : Finset G) = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg, Ne.symm hg2]),
          Finset.card_insert_of_notMem (by simpa using Ne.symm hg2g),
          Finset.card_singleton, hcard])
    intro x; simpa [← huniv] using Finset.mem_univ x
  -- g³ = 1 (it can't be g or g², by cancellation)
  have hg3 : g * g * g = 1 := by
    rcases helem (g * g * g) with h | h | h
    · exact h
    · exact absurd (Borcherds.Group.right_cancel g (g * g) 1 (by simp [h])) hg2
    · exact absurd (Borcherds.Group.left_cancel (g * g) g 1 (by rw [h]; simp)) hg
  have hg_g2 : g * (g * g) = 1 := by rw [← Borcherds.Group.mul_assoc]; exact hg3
  have hg2_g2 : (g * g) * (g * g) = g := by
    rw [Borcherds.Group.mul_assoc, hg_g2, Borcherds.Group.mul_one]
  -- Inverses: g⁻¹ = g², (g²)⁻¹ = g
  have hginv : g⁻¹ = g * g := ((Borcherds.Group.mul_eq_one_iff_right _ _).mp hg_g2).symm
  have hg2inv : (g * g)⁻¹ = g := ((Borcherds.Group.mul_eq_one_iff_right _ _).mp hg3).symm
  -- Build the isomorphism: 1 ↦ ⟨0⟩, g ↦ ⟨1⟩, g² ↦ ⟨2⟩
  exact {
    toEquiv := {
      toFun := fun x => if x = 1 then ⟨0⟩ else if x = g then ⟨1⟩ else ⟨2⟩
      invFun := fun y => if y.val = 0 then 1 else if y.val = 1 then g else g * g
      left_inv x := by grind [helem x]
      right_inv := by
        have key : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
        rintro ⟨y⟩
        rw [CyclicGroup.ext_iff]
        rcases key y with rfl | rfl | rfl <;>
          simp +decide [hg, hg2, hg2g, CyclicGroup.one_val]
    }
    map_mul x y := by
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl | rfl <;> rcases helem y with rfl | rfl | rfl <;>
        simp only [Borcherds.Group.one_mul, Borcherds.Group.mul_one, hg3, hg_g2, hg2_g2, if_neg hg, if_neg hg2, if_neg hg2g] <;>
        ext <;> simp +decide [CyclicGroup.mul_val, CyclicGroup.one_val]
    map_one := by simp [Equiv.coe_fn_mk]
    map_inv x := by
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl | rfl <;>
        simp only [Borcherds.Group.one_inv, hginv, hg2inv,
          if_neg hg, if_neg hg2, if_neg hg2g] <;>
        ext <;> simp +decide [CyclicGroup.one_val]
  }

/- Classification of groups of order 4 -/

/- The Klein four-group Z/2 × Z/2 -/
abbrev Klein4 := CyclicGroup 2 × CyclicGroup 2

instance : Mul Klein4 where
  mul a b := (a.1 * b.1, a.2 * b.2)

instance : One Klein4 where
  one := (1, 1)

instance : Inv Klein4 where
  inv a := (a.1⁻¹, a.2⁻¹)

instance : Borcherds.Group Klein4 where
  mul_assoc a b c := by ext <;> simp [Borcherds.Group.mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp
  mul_inv_cancel a := by ext <;> simp

inductive K4 : Type
  | one
  | a
  | b
  | c
  deriving Fintype, DecidableEq

instance : Mul K4 where
  mul r s :=
    match r, s with
    | .one, s => s
    | s, .one => s
    | .a, .a => .one
    | .b, .b => .one
    | .c, .c => .one
    | .a, .b => .c
    | .b, .a => .c
    | .a, .c => .b
    | .c, .a => .b
    | .b, .c => .a
    | .c, .b => .a

instance : One K4 where
  one := .one

instance : Inv K4 where
  inv r :=
    match r with
    | .one => .one
    | .a => .a
    | .b => .b
    | .c => .c

instance : Borcherds.Group K4 where
  mul_assoc := by decide +revert
  one_mul := by decide +revert
  mul_one := by decide +revert
  inv_mul_cancel := by decide +revert
  mul_inv_cancel := by decide +revert

/-- Every group of order 4 is isomorphic to Z/4 or to Z/2 × Z/2.
    The distinguishing invariant: does there exist an element of order > 2? -/
noncomputable def orderFourIso {G} [Borcherds.Group G] [Fintype G] (h : Nat.card G = 4) :
    Borcherds.GroupIso G (CyclicGroup 4) ⊕ Borcherds.GroupIso G Klein4 := by
  classical
  have hcard : Fintype.card G = 4 := by rwa [Nat.card_eq_fintype_card] at h
  -- Case split: does there exist an element of order > 2?
  by_cases h4 : ∃ g : G, g ≠ 1 ∧ g * g ≠ 1
  · /-
    Z/4 case: there exists g with g ≠ 1 and g² ≠ 1.
    The elements are {1, g, g², g³} and g⁴ = 1.
    -/
    let g : G := Classical.choose h4
    have hg : g ≠ 1 := (Classical.choose_spec h4).1
    have hg2 : g * g ≠ 1 := (Classical.choose_spec h4).2
    have hg2g : g * g ≠ g := fun heq => hg (Borcherds.Group.left_cancel g g 1 (by simp [heq]))
    -- g³ ≠ 1 (by Lagrange: {1, g, g²} would be subgroup of order 3, but 3 ∤ 4)
    have hg3 : g * g * g ≠ 1 := by
      intro hggg
      let H : BSubgroup G := {
        carrier := {1, g, g * g}
        one_mem := by simp
        mul_mem := fun x y hx hy => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            simp -failIfUnchanged
          · left; rw [← Borcherds.Group.mul_assoc]; exact hggg  -- g*(g²) = g³ = 1
          · left; exact hggg  -- g²*g = g³ = 1
          · -- g²*g² = g⁴ = g³*g = 1*g = g
            right; left
            calc (g * g) * (g * g)
                = ((g * g) * g) * g := by rw [← Borcherds.Group.mul_assoc]
              _ = 1 * g := by rw [hggg]
              _ = g := by simp
        inv_mem := fun x hx => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
          rcases hx with rfl | rfl | rfl
          · left; exact Borcherds.Group.one_inv
          · -- g⁻¹ = g² (since g²*g = g³ = 1)
            right; right
            exact ((Borcherds.Group.mul_eq_one_iff_left (g * g) g).mp hggg).symm
          · -- (g²)⁻¹ = g (since g²*g = g³ = 1)
            right; left
            exact ((Borcherds.Group.mul_eq_one_iff_right (g * g) g).mp hggg).symm
      }
      have hdvd := H.card_carrier_dvd_card
      rw [show H.carrier = ({1, g, g * g} : Set G) from rfl] at hdvd
      have : Set.ncard ({1, g, g * g} : Set G) = 3 := by
        rw [show ({1, g, g * g} : Set G) = {1, g, g * g} from rfl]
        rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hg, Ne.symm hg2])]
        rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hg2g])]
        simp
      rw [this, h] at hdvd
      omega
    -- g³ ≠ g, g³ ≠ g²
    have hg3g : g * g * g ≠ g := fun heq =>
      hg2 (Borcherds.Group.right_cancel g (g * g) 1 (by simp [heq]))
    have hg3g2 : g * g * g ≠ g * g := fun heq =>
      hg (Borcherds.Group.left_cancel (g * g) g 1 (by rw [heq]; simp))
    -- Every element is 1, g, g², or g³
    have helem : ∀ x : G, x = 1 ∨ x = g ∨ x = g * g ∨ x = g * g * g := by
      have hquad : ({1, g, g * g, g * g * g} : Finset G).card = Fintype.card G := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg, Ne.symm hg2, Ne.symm hg3]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hg2g, Ne.symm hg3g]),
            Finset.card_insert_of_notMem (by simpa using Ne.symm hg3g2),
            Finset.card_singleton, hcard]
      intro x
      have : x ∈ ({1, g, g * g, g * g * g} : Finset G) :=
        (Finset.eq_univ_of_card _ hquad) ▸ Finset.mem_univ x
      simpa using this
    -- g⁴ = 1
    have hg4 : g * g * g * g = 1 := by
      rcases helem (g * g * g * g) with h | h | h | h
      · exact h
      · exfalso; exact hg3 (Borcherds.Group.right_cancel g (g * g * g) 1 (by simp [h]))
      · exfalso; exact hg2 (Borcherds.Group.left_cancel (g * g) (g * g) 1 (by
          rw [Borcherds.Group.mul_assoc (g * g) g g] at h; simp [h]))
      · exfalso; exact hg (Borcherds.Group.left_cancel (g * g * g) g 1 (by simp [h]))
    -- Inverses
    have hginv : g⁻¹ = g * g * g := by
      have : g * (g * g * g) = 1 := by
        rw [← Borcherds.Group.mul_assoc g (g * g) g, ← Borcherds.Group.mul_assoc g g g]
        exact hg4
      exact ((Borcherds.Group.mul_eq_one_iff_right g (g * g * g)).mp this).symm
    have hg2inv : (g * g)⁻¹ = g * g := by
      -- (g²)⁻¹ = g² since g⁴ = 1 means (g²)² = 1
      have h : (g * g) * (g * g) = 1 := by
        rw [← Borcherds.Group.mul_assoc (g * g) g g]; exact hg4
      exact ((Borcherds.Group.mul_eq_one_iff_right (g * g) (g * g)).mp h).symm
    have hg3inv : (g * g * g)⁻¹ = g :=
      ((Borcherds.Group.mul_eq_one_iff_right (g * g * g) g).mp hg4).symm
    -- Multiplication facts
    have hg_g2 : g * (g * g) = g * g * g := by rw [Borcherds.Group.mul_assoc]
    have hg_g3 : g * (g * g * g) = 1 := by
      rw [← Borcherds.Group.mul_assoc g (g * g) g, ← Borcherds.Group.mul_assoc g g g]; exact hg4
    have hg2_g : (g * g) * g = g * g * g := rfl
    have hg2_g2 : (g * g) * (g * g) = 1 := by
      rw [← Borcherds.Group.mul_assoc]; exact hg4
    have hg2_g3 : (g * g) * (g * g * g) = g := by
      calc (g * g) * (g * g * g) = ((g * g) * (g * g)) * g := by rw [← Borcherds.Group.mul_assoc]
        _ = 1 * g := by rw [hg2_g2]
        _ = g := by simp
    have hg3_g : (g * g * g) * g = 1 := hg4
    have hg3_g2 : (g * g * g) * (g * g) = g := by
      calc (g * g * g) * (g * g)
          = ((g * g * g) * g) * g := by rw [← Borcherds.Group.mul_assoc]
        _ = 1 * g := by rw [hg4]
        _ = g := by simp
    have hg3_g3 : (g * g * g) * (g * g * g) = g * g := by
      calc (g * g * g) * (g * g * g)
          = ((g * g * g) * (g * g)) * g := by rw [← Borcherds.Group.mul_assoc]
        _ = g * g := by rw [hg3_g2]
    -- Build Z/4 isomorphism: 1 ↦ ⟨0⟩, g ↦ ⟨1⟩, g² ↦ ⟨2⟩, g³ ↦ ⟨3⟩
    exact Sum.inl {
      toEquiv := {
        toFun := fun x =>
          if x = 1 then ⟨0⟩ else if x = g then ⟨1⟩
          else if x = g * g then ⟨2⟩ else ⟨3⟩
        invFun := fun y =>
          if y.val = 0 then 1 else if y.val = 1 then g
          else if y.val = 2 then g * g else g * g * g
        left_inv x := by grind [helem x]
        right_inv := by
          have key : ∀ y : ZMod 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide
          rintro ⟨y⟩
          rw [CyclicGroup.ext_iff]
          rcases key y with rfl | rfl | rfl | rfl <;>
            simp +decide [hg, hg2, hg2g, hg3, hg3g, hg3g2, CyclicGroup.one_val]
      }
      map_mul x y := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          rcases helem y with rfl | rfl | rfl | rfl <;>
          simp only [Borcherds.Group.one_mul, Borcherds.Group.mul_one,
            hg_g2, hg_g3, hg2_g2, hg2_g3, hg3_g, hg3_g2, hg3_g3,
            if_neg hg, if_neg hg2, if_neg hg2g,
            if_neg hg3, if_neg hg3g, if_neg hg3g2] <;>
          ext <;> simp [CyclicGroup.mul_val, CyclicGroup.one_val] <;> decide
      map_one := by simp [Equiv.coe_fn_mk]
      map_inv x := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          simp only [Borcherds.Group.one_inv, hginv, hg2inv, hg3inv,
            if_neg hg, if_neg hg2, if_neg hg3,
            if_neg hg2g, if_neg hg3g, if_neg hg3g2] <;>
          ext <;> simp [CyclicGroup.inv_val, CyclicGroup.one_val] <;> decide
    }
  · /-
    Klein four case: every non-identity element has order 2.
    -/
    push Not at h4
    -- Every non-identity element squares to 1
    have hall2 : ∀ x : G, x ≠ 1 → x * x = 1 := h4
    -- Pick two distinct non-identity elements g, a
    have hne : ∃ g : G, g ≠ 1 := by
      by_contra hall; push Not at hall
      have : Fintype.card G ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b => by rw [hall a, hall b])
      omega
    let g : G := Classical.choose hne
    have hg : g ≠ 1 := Classical.choose_spec hne
    have hg2 : g * g = 1 := hall2 g hg
    have hne2 : ∃ a : G, a ≠ 1 ∧ a ≠ g := by
      by_contra hall; push Not at hall
      have : Finset.univ ⊆ ({1, g} : Finset G) := by
        intro x _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hx1 : x = 1
        · left; exact hx1
        · right; exact hall x hx1
      exact absurd (Finset.card_le_card this) (by
        rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hg),
            Finset.card_singleton, Finset.card_univ, hcard]; omega)
    let a : G := Classical.choose hne2
    have ha1 : a ≠ 1 := (Classical.choose_spec hne2).1
    have hag : a ≠ g := (Classical.choose_spec hne2).2
    have ha2 : a * a = 1 := hall2 a ha1
    -- The 4th element is a*g, distinct from 1, g, a
    have hag_ne1 : a * g ≠ 1 := by
      intro heq
      have haeq : a = g⁻¹ := (Borcherds.Group.mul_eq_one_iff_left a g).mp heq
      have hginveq : g⁻¹ = g := ((Borcherds.Group.mul_eq_one_iff_right g g).mp hg2).symm
      exact hag (haeq.trans hginveq)
    have hag_neg : a * g ≠ g :=
      fun heq => ha1 (Borcherds.Group.right_cancel g a 1 (by simp [heq]))
    have hag_nea : a * g ≠ a :=
      fun heq => hg (Borcherds.Group.left_cancel a g 1 (by simp [heq]))
    -- (a*g)² = 1
    have hag2 : (a * g) * (a * g) = 1 := hall2 (a * g) hag_ne1
    -- Every element is 1, g, a, or a*g
    have helem : ∀ x : G, x = 1 ∨ x = g ∨ x = a ∨ x = a * g := by
      have hquad : ({1, g, a, a * g} : Finset G).card = Fintype.card G := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg, Ne.symm ha1, Ne.symm hag_ne1]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hag, Ne.symm hag_neg]),
            Finset.card_insert_of_notMem (by simpa using Ne.symm hag_nea),
            Finset.card_singleton, hcard]
      intro x
      have : x ∈ ({1, g, a, a * g} : Finset G) :=
        (Finset.eq_univ_of_card _ hquad) ▸ Finset.mem_univ x
      simpa using this
    -- Commutativity: g*a = a*g
    have hga : g * a = a * g := by
      rcases helem (g * a) with h | h | h | h
      · exfalso; exact hag (((Borcherds.Group.mul_eq_one_iff_right g a).mp h).trans
            ((Borcherds.Group.mul_eq_one_iff_right g g).mp hg2).symm)
      · exfalso; exact ha1 (Borcherds.Group.left_cancel g a 1 (by simp [h]))
      · exfalso; exact hg (Borcherds.Group.right_cancel a g 1 (by simp [h]))
      · exact h
    -- Inverses (all self-inverse)
    have hginv : g⁻¹ = g := ((Borcherds.Group.mul_eq_one_iff_right g g).mp hg2).symm
    have hainv : a⁻¹ = a := ((Borcherds.Group.mul_eq_one_iff_right a a).mp ha2).symm
    have haginv : (a * g)⁻¹ = a * g :=
      ((Borcherds.Group.mul_eq_one_iff_right (a * g) (a * g)).mp hag2).symm
    -- Multiplication table
    have ha_ag : a * (a * g) = g := by rw [← Borcherds.Group.mul_assoc]; simp [ha2]
    have hg_ag : g * (a * g) = a := by
      calc g * (a * g) = (g * a) * g := by rw [Borcherds.Group.mul_assoc]
        _ = (a * g) * g := by rw [hga]
        _ = a * (g * g) := by rw [Borcherds.Group.mul_assoc]
        _ = a := by simp [hg2]
    have hag_a : (a * g) * a = g := by
      rw [Borcherds.Group.mul_assoc, hga, ← Borcherds.Group.mul_assoc, ha2, Borcherds.Group.one_mul]
    have hag_g : (a * g) * g = a := by
      rw [Borcherds.Group.mul_assoc]; simp [hg2]
    -- Build Klein4 isomorphism: 1↦(1,1), g↦(⟨1⟩,1), a↦(1,⟨1⟩), ag↦(⟨1⟩,⟨1⟩)
    exact Sum.inr {
      toEquiv := {
        toFun := fun x =>
          if x = 1 then (⟨0⟩, ⟨0⟩)
          else if x = g then (⟨1⟩, ⟨0⟩)
          else if x = a then (⟨0⟩, ⟨1⟩)
          else (⟨1⟩, ⟨1⟩)
        invFun := fun p =>
          if p.1.val = 0 && p.2.val = 0 then 1
          else if p.1.val = 1 && p.2.val = 0 then g
          else if p.1.val = 0 && p.2.val = 1 then a
          else a * g
        left_inv x := by grind [helem x]
        right_inv := by
          have key : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
          rintro ⟨⟨y1⟩, ⟨y2⟩⟩
          rcases key y1 with rfl | rfl <;> rcases key y2 with rfl | rfl <;>
            simp +decide [hg, ha1, hag, hag_ne1, hag_neg, hag_nea,
              Prod.ext_iff, CyclicGroup.ext_iff, CyclicGroup.one_val]
      }
      map_mul x y := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          rcases helem y with rfl | rfl | rfl | rfl <;>
          simp only [Borcherds.Group.one_mul, Borcherds.Group.mul_one,
            hg2, ha2, hag2, hga, ha_ag, hg_ag, hag_a, hag_g,
            if_neg hg, if_neg ha1, if_neg hag,
            if_neg hag_ne1, if_neg hag_neg, if_neg hag_nea,
            if_neg (Ne.symm hg), if_neg (Ne.symm ha1)] <;>
          ext <;> simp [CyclicGroup.mul_val, CyclicGroup.one_val] <;> decide
      map_one := by simp [Equiv.coe_fn_mk]
      map_inv x := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          simp only [Borcherds.Group.one_inv, hginv, hainv, haginv,
            if_neg hg, if_neg ha1, if_neg hag_ne1] <;>
          ext <;> simp [CyclicGroup.inv_val, CyclicGroup.one_val]
    }

noncomputable def orderFourIso' {G} [Borcherds.Group G] [Fintype G] (h : Nat.card G = 4) :
    Borcherds.GroupIso G (CyclicGroup 4) ⊕ Borcherds.GroupIso G K4 := by
  rcases orderFourIso h with hZ4 | hK4
  · exact Sum.inl hZ4
  · -- hK4 : GroupIso G Klein4 = GroupIso G (CyclicGroup 2 × CyclicGroup 2)
    -- Compose with the inverse of the K4 ≃ Klein4 mapping
    let toK4 : CyclicGroup 2 × CyclicGroup 2 → K4 := fun p => match p with
      | (⟨0⟩, ⟨0⟩) => .one
      | (⟨1⟩, ⟨0⟩) => .a
      | (⟨0⟩, ⟨1⟩) => .b
      | (⟨1⟩, ⟨1⟩) => .c
    let fromK4 : K4 → CyclicGroup 2 × CyclicGroup 2 := fun x => match x with
      | .one => (⟨0⟩, ⟨0⟩)
      | .a => (⟨1⟩, ⟨0⟩)
      | .b => (⟨0⟩, ⟨1⟩)
      | .c => (⟨1⟩, ⟨1⟩)
    have hleft : ∀ p, fromK4 (toK4 p) = p := by
      intro ⟨⟨a⟩, ⟨b⟩⟩; fin_cases a <;> fin_cases b <;> rfl
    have hright : ∀ x, toK4 (fromK4 x) = x := by
      intro x; cases x <;> rfl
    have htoK4_mul : ∀ a b, toK4 (a * b) = toK4 a * toK4 b := by
      intro ⟨⟨a1⟩, ⟨a2⟩⟩ ⟨⟨b1⟩, ⟨b2⟩⟩
      fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;> decide
    have htoK4_one : toK4 1 = 1 := by decide
    have htoK4_inv : ∀ a, toK4 a⁻¹ = (toK4 a)⁻¹ := by
      intro ⟨⟨a1⟩, ⟨a2⟩⟩; fin_cases a1 <;> fin_cases a2 <;> decide
    let ps : CyclicGroup 2 × CyclicGroup 2 ≃ K4 := {
      toFun := toK4
      invFun := fromK4
      left_inv := hleft
      right_inv := hright
    }
    exact Sum.inr {
      toEquiv := hK4.toEquiv.trans ps
      map_mul := fun x y => by
        show toK4 (hK4.toEquiv (x * y)) = toK4 (hK4.toEquiv x) * toK4 (hK4.toEquiv y)
        rw [hK4.map_mul, htoK4_mul]
      map_one := by
        show toK4 (hK4.toEquiv 1) = 1
        rw [hK4.map_one, htoK4_one]
      map_inv := fun x => by
        show toK4 (hK4.toEquiv x⁻¹) = (toK4 (hK4.toEquiv x))⁻¹
        rw [hK4.map_inv, htoK4_inv]
    }


/- Powers of a group element -/

section Powers

variable {G : Type*} [Borcherds.Group G]

def npow (g : G) : ℕ → G
  | 0 => 1
  | n + 1 => npow g n * g

@[simp] lemma Bnpow_zero (g : G) : npow g 0 = 1 := rfl
@[simp] lemma npow_succ (g : G) (n : ℕ) : npow g (n + 1) = npow g n * g := rfl
@[simp] lemma Bnpow_one (g : G) : npow g 1 = g := by simp [npow]

lemma Bnpow_add (g : G) (m n : ℕ) : npow g (m + n) = npow g m * npow g n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_succ, npow_succ, npow_succ, ih, Borcherds.Group.mul_assoc]

end Powers

/- Cyclic subgroups -/

section CyclicSubgroup

variable {G : Type*} [Borcherds.Group G]

/-- For g with gᵐ = 1 (m > 0), the set {gᵏ | k < m} is a subgroup. -/
def cyclicSubgroup (g : G) (m : ℕ) (hm : 0 < m) (hgm : npow g m = 1) : BSubgroup G where
  carrier := { x | ∃ k, k < m ∧ npow g k = x }
  one_mem := ⟨0, hm, rfl⟩
  mul_mem := by
    rintro x y ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    by_cases h : i + j < m
    · exact ⟨i + j, h, Bnpow_add g i j⟩
    · refine ⟨i + j - m, by omega, ?_⟩
      -- Goal: npow g (i+j-m) = npow g i * npow g j
      -- npow g i * npow g j = npow g (i+j) = npow g ((i+j-m)+m) = npow g (i+j-m) * npow g m
      --   = npow g (i+j-m) * 1 = npow g (i+j-m)
      have hstep1 : npow g i * npow g j = npow g (i + j) := (Bnpow_add g i j).symm
      have hstep2 : npow g (i + j) = npow g (i + j - m) * npow g m := by
        conv_lhs => rw [show i + j = (i + j - m) + m from by omega]
        exact Bnpow_add g (i + j - m) m
      rw [hstep1, hstep2, hgm, Borcherds.Group.mul_one]
  inv_mem := by
    rintro x ⟨i, hi, rfl⟩
    by_cases h : i = 0
    · subst h; simp [Borcherds.Group.one_inv]; exact ⟨0, hm, rfl⟩
    · refine ⟨m - i, by omega, ?_⟩
      have : npow g i * npow g (m - i) = 1 := by
        rw [← Bnpow_add, show i + (m - i) = m from by omega, hgm]
      exact (Borcherds.Group.mul_eq_one_iff_right (npow g i) (npow g (m - i))).mp this

/-- If npow g is injective on {0,...,m-1}, the cyclic subgroup has m elements. -/
lemma ncard_cyclicSubgroup (g : G) (m : ℕ) (hm : 0 < m) (hgm : npow g m = 1)
    (hinj : ∀ i j, i < m → j < m → npow g i = npow g j → i = j) :
    Set.ncard (cyclicSubgroup g m hm hgm).carrier = m := by
  have hset : (cyclicSubgroup g m hm hgm).carrier = (npow g) '' (Finset.range m : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_range.mpr hk))
    · rintro ⟨k, hk, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      exact ⟨k, hk, rfl⟩
  rw [hset]
  have hfin : Set.Finite (Finset.range m : Set ℕ) := Finset.finite_toSet _
  have hinjOn : Set.InjOn (npow g) (Finset.range m : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    exact hinj a b ha hb hab
  rw [hinjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]

end CyclicSubgroup

/- Classification of groups of order p, p prime -/

section PrimeOrder

attribute [local instance] Classical.propDecidable

variable {G : Type*} [Borcherds.Group G] [Fintype G]

/-- In a finite group, every element has finite order: ∃ k > 0, gᵏ = 1. -/
lemma exists_npow_eq_one (g : G) : ∃ k : ℕ, 0 < k ∧ npow g k = 1 := by
  -- By pigeonhole, npow g can't be injective on Fin (|G| + 1)
  by_contra hall
  push Not at hall
  have hall' : ∀ k : ℕ, 0 < k → npow g k ≠ 1 := fun k hk => hall k hk
  have hinj : Function.Injective (fun i : Fin (Fintype.card G + 1) => npow g i.val) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.mk.injEq]
    simp only at hij
    by_contra hne
    -- WLOG i < j
    have hlt : i < j ∨ j < i := by omega
    rcases hlt with h | h
    · have heq : npow g (j - i) = 1 := by
        have hadd := Bnpow_add g (j - i) i
        rw [show (j - i) + i = j from by omega] at hadd
        -- hadd : npow g j = npow g (j-i) * npow g i
        -- hij : npow g i = npow g j
        -- so npow g (j-i) * npow g i = npow g i = 1 * npow g i
        exact Borcherds.Group.right_cancel (npow g i) (npow g (j - i)) 1
          (by rw [← hadd, hij, Borcherds.Group.one_mul])
      exact hall' (j - i) (by omega) heq
    · have heq : npow g (i - j) = 1 := by
        have hadd := Bnpow_add g (i - j) j
        rw [show (i - j) + j = i from by omega] at hadd
        exact Borcherds.Group.right_cancel (npow g j) (npow g (i - j)) 1
          (by rw [← hadd, ← hij, Borcherds.Group.one_mul])
      exact hall' (i - j) (by omega) heq
  have hle := Fintype.card_le_of_injective _ hinj
  simp [Fintype.card_fin] at hle

/-- The order of g: smallest positive k with gᵏ = 1. -/
noncomputable def elemOrder (g : G) : ℕ :=
  Nat.find (exists_npow_eq_one g)

lemma elemOrder_pos (g : G) : 0 < elemOrder g :=
  (Nat.find_spec (exists_npow_eq_one g)).1

lemma npow_elemOrder (g : G) : npow g (elemOrder g) = 1 :=
  (Nat.find_spec (exists_npow_eq_one g)).2

lemma elemOrder_minimal (g : G) (k : ℕ) (hk : 0 < k) (hgk : npow g k = 1) :
    elemOrder g ≤ k :=
  Nat.find_min' (exists_npow_eq_one g) ⟨hk, hgk⟩

/-- npow g is injective on {0, ..., elemOrder g - 1}. -/
lemma npow_injective_of_order (g : G) (i j : ℕ)
    (hi : i < elemOrder g) (hj : j < elemOrder g) (hij : npow g i = npow g j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have heq : npow g (j - i) = 1 := by
      have hadd := Bnpow_add g (j - i) i
      rw [show (j - i) + i = j from by omega] at hadd
      exact Borcherds.Group.right_cancel (npow g i) (npow g (j - i)) 1
        (by rw [← hadd, hij, Borcherds.Group.one_mul])
    have hle := elemOrder_minimal g (j - i) (by omega) heq
    omega
  · have heq : npow g (i - j) = 1 := by
      have hadd := Bnpow_add g (i - j) j
      rw [show (i - j) + j = i from by omega] at hadd
      exact Borcherds.Group.right_cancel (npow g j) (npow g (i - j)) 1
        (by rw [← hadd, ← hij, Borcherds.Group.one_mul])
    have hle := elemOrder_minimal g (i - j) (by omega) heq
    omega

/-- The order of g divides |G|. -/
lemma elemOrder_dvd_card (g : G) : elemOrder g ∣ Nat.card G := by
  have hm := elemOrder_pos g
  have hgm := npow_elemOrder g
  let H := cyclicSubgroup g (elemOrder g) hm hgm
  have hdvd : H.carrier.ncard ∣ Nat.card G := H.card_carrier_dvd_card
  have hcard : H.carrier.ncard = elemOrder g :=
    ncard_cyclicSubgroup g (elemOrder g) hm hgm (npow_injective_of_order g)
  rwa [hcard] at hdvd

/-- g ≠ 1 implies elemOrder g > 1. -/
lemma elemOrder_gt_one (g : G) (hg : g ≠ 1) : elemOrder g > 1 := by
  have hpos := elemOrder_pos g
  by_contra h
  push Not at h
  have heq : elemOrder g = 1 := by omega
  have : npow g (elemOrder g) = 1 := npow_elemOrder g
  rw [heq, Bnpow_one] at this
  exact hg this

/- Isomorphism from a group of prime order to `CyclicGroup p` (noncanonical generator choice). -/
noncomputable def myIso (hp : (Nat.card G).Prime) :
    Borcherds.GroupIso G (CyclicGroup (Nat.card G)) := by
  classical
  set p := Nat.card G with hp_def
  have hcard : Fintype.card G = p := by rw [← Nat.card_eq_fintype_card]
  -- Pick g ≠ 1
  have hne : ∃ g : G, g ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Fintype.card G ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => by rw [hall a, hall b])
    rw [hcard] at this; exact absurd hp.one_lt (by omega)
  let g : G := Classical.choose hne
  have hg : g ≠ 1 := Classical.choose_spec hne
  -- The order of g equals p (divides p, is > 1, p is prime)
  have hord : elemOrder g = p := by
    have hdvd := elemOrder_dvd_card g
    have hgt := elemOrder_gt_one g hg
    exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left (by omega)
  -- npow g : Fin p → G is injective, hence bijective
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hinj : Function.Injective (fun k : Fin p => npow g k.val) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij; simp only [Fin.mk.injEq]
    exact npow_injective_of_order g i j (hord ▸ hi) (hord ▸ hj) hij
  have hbij : Function.Bijective (fun k : Fin p => npow g k.val) :=
    ⟨hinj, hinj.surjective_of_finite (Fintype.equivOfCardEq (by simp [hcard]))⟩
  -- npow g is periodic with period p
  have hgp : npow g p = 1 := hord ▸ npow_elemOrder g
  have npow_mul_p : ∀ k, npow g (k * p) = 1 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, Bnpow_add, ih, Borcherds.Group.one_mul, hgp]
  have npow_mod : ∀ k, npow g k = npow g (k % p) := by
    intro k
    conv_lhs => rw [show k = k % p + (k / p) * p from by linarith [Nat.div_add_mod k p]]
    rw [Bnpow_add, npow_mul_p, Borcherds.Group.mul_one]
  -- The discrete log: inverse of npow g on Fin p
  let f := Equiv.ofBijective (fun k : Fin p => npow g k.val) hbij
  -- Spec lemmas
  have f_apply : ∀ k : Fin p, f k = npow g k.val := fun _ => rfl
  have f_symm_spec : ∀ x : G, npow g (f.symm x).val = x :=
    fun x => f.apply_symm_apply x
  have f_symm_apply : ∀ k : Fin p, f.symm (npow g k.val) = k :=
    fun k => f.symm_apply_apply k
  -- Key: f.symm is an "additive-to-multiplicative" map
  -- f.symm(x * y) = f.symm(x) + f.symm(y) in Fin p (= ZMod p)
  have f_symm_mul : ∀ x y : G, f.symm (x * y) = f.symm x + f.symm y := by
    intro x y
    apply hinj; simp only
    -- LHS: npow g (f.symm (x * y)).val = x * y
    rw [f_symm_spec]
    -- RHS: npow g (f.symm x + f.symm y).val
    -- In Fin p (= ZMod p for p ≥ 2): (a + b).val = (a.val + b.val) % p
    rw [show (f.symm x + f.symm y).val = (((f.symm x).val + (f.symm y).val) % p) from
      Fin.val_add (f.symm x) (f.symm y)]
    rw [← npow_mod, Bnpow_add, f_symm_spec, f_symm_spec]
  haveI hNeZero : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩
  have fin_cast_zmod : ∀ a : Fin p, ZMod.val (a : ZMod p) = a.val :=
    fun a => by simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  have f_symm_one : f.symm 1 = 0 := by
    apply hinj; simp only
    rw [f_symm_spec, Fin.val_zero, Bnpow_zero]
  have f_symm_inv : ∀ x : G, f.symm x⁻¹ = -(f.symm x) := by
    intro x; apply hinj; simp only
    rw [f_symm_spec, Fin.val_neg' (f.symm x), ← npow_mod]
    have hk : (f.symm x).val < p := (f.symm x).isLt
    have hsum : npow g (p - (f.symm x).val) * npow g (f.symm x).val = 1 := by
      rw [← Bnpow_add, show (p - (f.symm x).val) + (f.symm x).val = p from by omega, hgp]
    exact (((Borcherds.Group.mul_eq_one_iff_left
        (npow g (p - (f.symm x).val)) (npow g (f.symm x).val)).mp hsum).trans
      (by rw [f_symm_spec])).symm
  -- Coercion lemmas: Fin p operation cast to ZMod p
  have cast_add : ∀ a b : Fin p, ((a + b : Fin p) : ZMod p) = (a : ZMod p) + (b : ZMod p) :=
    fun a b => by simp [Fin.val_add]
  have cast_neg : ∀ a : Fin p, ((-a : Fin p) : ZMod p) = -(a : ZMod p) :=
    fun a => by simp [Fin.val_neg']
  have cast_zero : ((0 : Fin p) : ZMod p) = 0 := by simp
  -- Build GroupIso: x ↦ ⟨↑(f.symm x)⟩, inverse ⟨k⟩ ↦ npow g (ZMod.val k)
  exact (show Borcherds.GroupIso G (CyclicGroup p) from {
    toEquiv := {
      toFun := fun x => ⟨(f.symm x : ZMod p)⟩
      invFun := fun ⟨k⟩ => npow g (ZMod.val k)
      left_inv := fun x => by
        simp only [fin_cast_zmod]
        exact f_symm_spec x
      right_inv := fun ⟨k⟩ => by
        ext
        simp only
        have hlt : ZMod.val k < p := ZMod.val_lt k
        have h := f_symm_apply ⟨ZMod.val k, hlt⟩
        -- h : f.symm (npow g (ZMod.val k)) = ⟨ZMod.val k, hlt⟩ : Fin p
        -- Need: (f.symm (npow g (ZMod.val k)) : ZMod p) = k
        have : (f.symm (npow g (ZMod.val k)) : ZMod p) = ((⟨ZMod.val k, hlt⟩ : Fin p) : ZMod p) :=
          congr_arg (fun a : Fin p => (a : ZMod p)) h
        rw [this]
        simp
    }
    map_mul := fun x y => by
      ext
      simp only [Equiv.coe_fn_mk, CyclicGroup.mul_val]
      -- goal: (f.symm (x * y) : ZMod p) = (f.symm x : ZMod p) + (f.symm y : ZMod p)
      rw [congr_arg (fun a : Fin p => (a : ZMod p)) (f_symm_mul x y)]
      exact cast_add (f.symm x) (f.symm y)
    map_one := by
      ext
      simp only [Equiv.coe_fn_mk, CyclicGroup.one_val]
      -- goal: (f.symm 1 : ZMod p) = 0
      rw [congr_arg (fun a : Fin p => (a : ZMod p)) f_symm_one]
      exact cast_zero
    map_inv := fun x => by
      ext
      simp only [Equiv.coe_fn_mk, CyclicGroup.inv_val]
      -- goal: (f.symm x⁻¹ : ZMod p) = -(f.symm x : ZMod p)
      rw [congr_arg (fun a : Fin p => (a : ZMod p)) (f_symm_inv x)]
      exact cast_neg (f.symm x)
  })

end PrimeOrder

/-
Definition 1.12 (Product)
-/
instance {G H} [Borcherds.Group G] [Borcherds.Group H] : Mul (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)

instance {G H} [Borcherds.Group G] [Borcherds.Group H] : One (G × H) where
  one := (1, 1)

instance {G H} [Borcherds.Group G] [Borcherds.Group H] : Inv (G × H) where
  inv a := (a.1⁻¹, a.2⁻¹)

instance {G H} [Borcherds.Group G] [Borcherds.Group H] : Borcherds.Group (G × H) where
  mul_assoc a b c := by ext <;> simp [Borcherds.Group.mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp [Borcherds.Group.inv_mul_cancel]
  mul_inv_cancel a := by ext <;> simp [Borcherds.Group.mul_inv_cancel]

/-
Example 1.8.a
-/
def productIso : Borcherds.GroupIso K4 (CyclicGroup 2 × CyclicGroup 2) := {
  toEquiv := {
    toFun := fun x => match x with
      | .one => (⟨0⟩, ⟨0⟩)
      | .a => (⟨1⟩, ⟨0⟩)
      | .b => (⟨0⟩, ⟨1⟩)
      | .c => (⟨1⟩, ⟨1⟩)
    invFun := fun p => match p with
      | (⟨0⟩, ⟨0⟩) => .one
      | (⟨1⟩, ⟨0⟩) => .a
      | (⟨0⟩, ⟨1⟩) => .b
      | (⟨1⟩, ⟨1⟩) => .c
    left_inv := by intro x; cases x <;> decide
    right_inv := by intro ⟨⟨a⟩, ⟨b⟩⟩; fin_cases a <;> fin_cases b <;> rfl
  }
  map_mul := by intro x y; cases x <;> cases y <;> ext <;> simp +decide
  map_one := rfl
  map_inv := by intro x; cases x <;> ext <;> simp
}

/-
Example 1.9 - omitted
-/

/-
Proposition 1.7, part 1
-/
def leftCopy {G} [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : BSubgroup (H₁ × H₂) where
  carrier := { p | p.2 = 1 }
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

def rightCopy {G} [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : BSubgroup (H₁ × H₂) where
  carrier := { p | p.1 = 1 }
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

/-
Definition: a group is isomorphic to the product of two of its subgroups
-/
def IsIsomorphicToProductOfSubgroups (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  Nonempty (Borcherds.GroupIso (H₁ × H₂) G)

def s₁ : BSubgroup K4 := {
  carrier := { .one, .a }
  one_mem := by decide
  mul_mem := by decide
  inv_mem := by decide
}

def s₂ : BSubgroup K4 := {
  carrier := { .one, .b }
  one_mem := by decide
  mul_mem := by decide
  inv_mem := by decide
}

def s₃ : BSubgroup K4 := {
  carrier := { .one, .c }
  one_mem := by decide
  mul_mem := by decide
  inv_mem := by decide
}

example : IsIsomorphicToProductOfSubgroups K4 s₁ s₂ := by sorry

def HasTrivialIntersection (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  H₁.carrier ∩ H₂.carrier = {1}

def HasUniqueDecomposition (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∀ g : G, ∃ h₁ ∈ H₁.carrier, ∃ h₂ ∈ H₂.carrier, g = h₁ * h₂

def HasCommutingSubgroups (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∀ h₁ ∈ H₁.carrier, ∀ h₂ ∈ H₂.carrier, h₁ * h₂ = h₂ * h₁

example : HasTrivialIntersection K4 s₁ s₂ := by
  simp only [HasTrivialIntersection, s₁, s₂]
  ext x
  decide +revert

example : HasUniqueDecomposition K4 s₁ s₂ := by
  simp only [HasUniqueDecomposition, s₁, s₂]
  intro g
  fin_cases g <;> decide -- decide is a bit powerful here, it's closing existential goals of the form `∃ ...`

example : HasCommutingSubgroups K4 s₁ s₂ := by
  simp only [HasCommutingSubgroups, s₁, s₂]
  intro h₁ hh₁ h₂ hh₂
  decide +revert

/-
The recognition theorem (← direction only).
The forward direction fails for the weak definition IsIsomorphicToProductOfSubgroups:
  Counterexample: G = K4, H₁ = H₂ = {1, a}. Then H₁ × H₂ ≅ Z/2 × Z/2 ≅ K4 = G,
  but H₁ ∩ H₂ = {1, a} ≠ {1}.
See IsIsomorphicToProductOfSubgroups' below for the corrected biconditional.
-/

/- Helper: uniqueness of decomposition from trivial intersection -/
private lemma decomp_unique {G} [Borcherds.Group G] {H₁ H₂ : BSubgroup G}
    (htrivial : HasTrivialIntersection G H₁ H₂)
    {a₁ b₁ a₂ b₂ : G}
    (ha₁ : a₁ ∈ H₁.carrier) (hb₁ : b₁ ∈ H₁.carrier)
    (ha₂ : a₂ ∈ H₂.carrier) (hb₂ : b₂ ∈ H₂.carrier)
    (heq : a₁ * a₂ = b₁ * b₂) : a₁ = b₁ ∧ a₂ = b₂ := by
  -- Show b₁⁻¹ * a₁ ∈ H₁ ∩ H₂ = {1}
  have hkey : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
    apply Borcherds.Group.left_cancel b₁
    apply Borcherds.Group.right_cancel a₂
    calc b₁ * (b₁⁻¹ * a₁) * a₂
        = (b₁ * b₁⁻¹) * a₁ * a₂ := by
          rw [← Borcherds.Group.mul_assoc b₁ b₁⁻¹ a₁, Borcherds.Group.mul_assoc]
      _ = a₁ * a₂ := by simp
      _ = b₁ * b₂ := heq
      _ = b₁ * (b₂ * (a₂⁻¹ * a₂)) := by simp
      _ = b₁ * (b₂ * a₂⁻¹) * a₂ := by
          rw [← Borcherds.Group.mul_assoc b₂ a₂⁻¹ a₂, ← Borcherds.Group.mul_assoc]
  have hmem : b₁⁻¹ * a₁ ∈ H₁.carrier ∩ H₂.carrier :=
    ⟨H₁.mul_mem _ _ (H₁.inv_mem _ hb₁) ha₁, hkey ▸ H₂.mul_mem _ _ hb₂ (H₂.inv_mem _ ha₂)⟩
  rw [htrivial] at hmem
  have h1 : b₁⁻¹ * a₁ = 1 := Set.mem_singleton_iff.mp hmem
  constructor
  · exact Borcherds.Group.left_cancel b₁⁻¹ a₁ b₁ (by simp [h1])
  · have : a₁ = b₁ := Borcherds.Group.left_cancel b₁⁻¹ a₁ b₁ (by simp [h1])
    rw [this] at heq
    exact Borcherds.Group.left_cancel b₁ a₂ b₂ heq

/- Helper: the four-term associativity rearrangement using commutativity -/
private lemma mul_mul_comm {G} [Borcherds.Group G] {H₁ H₂ : BSubgroup G}
    (hcommute : HasCommutingSubgroups G H₁ H₂)
    {a₁ b₁ : G} {a₂ b₂ : G}
    (_ha₁ : a₁ ∈ H₁.carrier) (hb₁ : b₁ ∈ H₁.carrier)
    (ha₂ : a₂ ∈ H₂.carrier) (_hb₂ : b₂ ∈ H₂.carrier)
    : (a₁ * b₁) * (a₂ * b₂) = (a₁ * a₂) * (b₁ * b₂) := by
  -- Need: a₂ * b₁ = b₁ * a₂ (from commutativity, with b₁ ∈ H₁, a₂ ∈ H₂)
  have hc : b₁ * a₂ = a₂ * b₁ := hcommute b₁ hb₁ a₂ ha₂
  calc (a₁ * b₁) * (a₂ * b₂)
      = a₁ * (b₁ * (a₂ * b₂)) := by rw [Borcherds.Group.mul_assoc]
    _ = a₁ * ((b₁ * a₂) * b₂) := by rw [← Borcherds.Group.mul_assoc b₁ a₂ b₂]
    _ = a₁ * ((a₂ * b₁) * b₂) := by rw [hc]
    _ = a₁ * (a₂ * (b₁ * b₂)) := by rw [Borcherds.Group.mul_assoc a₂ b₁ b₂]
    _ = (a₁ * a₂) * (b₁ * b₂) := by rw [← Borcherds.Group.mul_assoc]

/- Core construction: build a GroupIso from the three conditions -/
noncomputable def mulMapIso {G} [Borcherds.Group G] {H₁ H₂ : BSubgroup G}
    (htrivial : HasTrivialIntersection G H₁ H₂)
    (hdecomp : HasUniqueDecomposition G H₁ H₂)
    (hcommute : HasCommutingSubgroups G H₁ H₂)
    : Borcherds.GroupIso (H₁ × H₂) G := by
  classical
  -- Extract decomposition functions
  have hspec := fun g => Classical.choose_spec (hdecomp g)
  let d₁ : G → G := fun g => Classical.choose (hdecomp g)
  have hd₁_mem : ∀ g, d₁ g ∈ H₁.carrier := fun g => (hspec g).1
  have hspec₂ := fun g => Classical.choose_spec (hspec g).2
  let d₂ : G → G := fun g => Classical.choose (hspec g).2
  have hd₂_mem : ∀ g, d₂ g ∈ H₂.carrier := fun g => (hspec₂ g).1
  have hd_eq : ∀ g, g = d₁ g * d₂ g := fun g => (hspec₂ g).2
  exact {
    toEquiv := {
      toFun := fun p => p.1.val * p.2.val
      invFun := fun g => (⟨d₁ g, hd₁_mem g⟩, ⟨d₂ g, hd₂_mem g⟩)
      left_inv := by
        intro ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩⟩
        simp only
        have hu := decomp_unique htrivial (hd₁_mem (h₁ * h₂)) hh₁
          (hd₂_mem (h₁ * h₂)) hh₂ (hd_eq (h₁ * h₂)).symm
        exact Prod.ext (Subtype.ext hu.1) (Subtype.ext hu.2)
      right_inv := by
        intro g; simp only; exact (hd_eq g).symm
    }
    map_mul := by
      intro ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩⟩
      show (a₁ * b₁) * (a₂ * b₂) = (a₁ * a₂) * (b₁ * b₂)
      exact mul_mul_comm hcommute ha₁ hb₁ ha₂ hb₂
    map_one := by
      show (1 : G) * 1 = 1
      simp
    map_inv := by
      intro ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩
      show a₁⁻¹ * a₂⁻¹ = (a₁ * a₂)⁻¹
      rw [Borcherds.Group.mul_inv]
      exact hcommute a₁⁻¹ (H₁.inv_mem _ ha₁) a₂⁻¹ (H₂.inv_mem _ ha₂)
  }

@[simp]
lemma mulMapIso_apply {G} [Borcherds.Group G] {H₁ H₂ : BSubgroup G}
    (htrivial : HasTrivialIntersection G H₁ H₂)
    (hdecomp : HasUniqueDecomposition G H₁ H₂)
    (hcommute : HasCommutingSubgroups G H₁ H₂)
    (h₁ : H₁) (h₂ : H₂)
    : (mulMapIso htrivial hdecomp hcommute).toEquiv (h₁, h₂) = h₁.val * h₂.val := rfl

theorem recognition_backward (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G)
    (htrivial : HasTrivialIntersection G H₁ H₂)
    (hdecomp : HasUniqueDecomposition G H₁ H₂)
    (hcommute : HasCommutingSubgroups G H₁ H₂)
    : IsIsomorphicToProductOfSubgroups G H₁ H₂ :=
  ⟨mulMapIso htrivial hdecomp hcommute⟩

/-
Strengthened definition: the isomorphism must be the multiplication map (h₁, h₂) ↦ h₁ · h₂.
With this definition, both directions of the recognition theorem hold.
-/
def IsIsomorphicToProductOfSubgroups' (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∃ (φ : Borcherds.GroupIso (H₁ × H₂) G), ∀ (h₁ : H₁) (h₂ : H₂), φ.toEquiv (h₁, h₂) = h₁.val * h₂.val

example : (K4.a ∈ s₁.carrier) := by simp [s₁]

example : ¬ (K4.a ∈ s₂.carrier) := by simp [s₂]

example : ¬  (K4.b ∈ s₁.carrier) := by simp [s₁]

def K4.s12Equiv : ({ x // x ∈ s₁.carrier } × { x // x ∈ s₂.carrier }) ≃ K4 where
  toFun := fun p => match p with
    | (⟨.one, _⟩, ⟨.one, _⟩) => .one
    | (⟨.a, _⟩, ⟨.one, _⟩) => .a
    | (⟨.one, _⟩, ⟨.b, _⟩) => .b
    | (⟨.a, _⟩, ⟨.b, _⟩) => .c
  invFun := fun x => match x with -- could a *tactic* come up with the inverse?
    | .one => (⟨.one, by simp [s₁]⟩, ⟨.one, by simp [s₂]⟩)
    | .a => (⟨.a, by simp [s₁]⟩, ⟨.one, by simp [s₂]⟩)
    | .b => (⟨.one, by simp [s₁]⟩, ⟨.b, by simp [s₂]⟩)
    | .c => (⟨.a, by simp [s₁]⟩, ⟨.b, by simp [s₂]⟩)

  -- Would these proofs be easier if the carrier were a `Finset`?
  -- idea for a tactic, make `fin_cases` work on hypotheses `x ∈ {...}` and `0 ≤ x ≤ 10` and `a | 10`
  left_inv := by
    simp only [Function.LeftInverse, Prod.forall, Subtype.forall]
    intro x hx y hy
    simp only [s₁, s₂] at hx hy
    fin_cases x <;> fin_cases y <;> simp at hx hy ⊢
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse]
    intro x
    fin_cases x
    <;> simp

def K4.s12Iso : Borcherds.GroupIso ({ x // x ∈ s₁.carrier } × { x // x ∈ s₂.carrier }) K4 where
  toEquiv := s12Equiv
  map_mul := by
    rintro ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩
    simp only [s₁, s₂] at hx1 hx2 hy1 hy2
    fin_cases x1 <;> simp at hx1
    <;> fin_cases x2 <;> simp at hx2
    <;> fin_cases y1 <;> simp at hy1
    <;> fin_cases y2 <;> simp at hy2
    <;> rfl
  map_one := by
    simp only [s12Equiv]
    rfl
  map_inv := by
    rintro ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩
    simp only [s₁, s₂] at hx1 hx2
    fin_cases x1 <;> simp at hx1
    <;> fin_cases x2 <;> simp at hx2
    <;> rfl

example : IsIsomorphicToProductOfSubgroups' K4 s₁ s₂ := by
  rw [IsIsomorphicToProductOfSubgroups']
  sorry

theorem recognition_theorem (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G)
    : IsIsomorphicToProductOfSubgroups' G H₁ H₂ ↔
      (HasTrivialIntersection G H₁ H₂ ∧ HasUniqueDecomposition G H₁ H₂ ∧ HasCommutingSubgroups G H₁ H₂) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨?_, ?_, ?_⟩
    · -- Trivial intersection
      simp only [HasTrivialIntersection]
      ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx₁, hx₂⟩
        -- φ(⟨x, hx₁⟩, ⟨x⁻¹, _⟩) = x * x⁻¹ = 1 = φ(1, 1)
        have h1 : φ.toEquiv (⟨x, hx₁⟩, ⟨x⁻¹, H₂.inv_mem x hx₂⟩) = 1 := by
          rw [hφ]; simp
        have h2 : φ.toEquiv (⟨1, H₁.one_mem⟩, ⟨1, H₂.one_mem⟩) = 1 := by
          rw [hφ]; simp
        have hinj := φ.toEquiv.injective (h1.trans h2.symm)
        exact (Prod.ext_iff.mp hinj).1 |> Subtype.ext_iff.mp |> fun h => h
      · rintro rfl; exact ⟨H₁.one_mem, H₂.one_mem⟩
    · -- Unique decomposition
      simp only [HasUniqueDecomposition]
      intro g
      obtain ⟨⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩⟩, hg⟩ := φ.toEquiv.surjective g
      rw [hφ] at hg
      exact ⟨h₁, hh₁, h₂, hh₂, hg.symm⟩
    · -- Commuting subgroups
      simp only [HasCommutingSubgroups]
      intro h₁ hh₁ h₂ hh₂
      -- Name the key elements of H₁ × H₂
      let p₁₀ : H₁ × H₂ := (⟨h₁, hh₁⟩, ⟨1, H₂.one_mem⟩)
      let p₀₂ : H₁ × H₂ := (⟨1, H₁.one_mem⟩, ⟨h₂, hh₂⟩)
      -- φ maps (h₁, 1) to h₁ and (1, h₂) to h₂
      have hφ₁ : φ.toEquiv p₁₀ = h₁ := by simp only [p₁₀]; rw [hφ]; simp
      have hφ₂ : φ.toEquiv p₀₂ = h₂ := by simp only [p₀₂]; rw [hφ]; simp
      -- In H₁ × H₂, (h₁, 1) * (1, h₂) = (1, h₂) * (h₁, 1)
      have hprod : p₁₀ * p₀₂ = p₀₂ * p₁₀ := by
        apply Prod.ext
        · exact Subtype.ext (show h₁ * 1 = 1 * h₁ by simp)
        · exact Subtype.ext (show (1 : G) * h₂ = h₂ * 1 by simp)
      calc h₁ * h₂
          = φ.toEquiv p₁₀ * φ.toEquiv p₀₂ := by rw [hφ₁, hφ₂]
        _ = φ.toEquiv (p₁₀ * p₀₂) := (φ.map_mul _ _).symm
        _ = φ.toEquiv (p₀₂ * p₁₀) := by rw [hprod]
        _ = φ.toEquiv p₀₂ * φ.toEquiv p₁₀ := φ.map_mul _ _
        _ = h₂ * h₁ := by rw [hφ₁, hφ₂]
  · -- Backward: three conditions → strengthened iso
    rintro ⟨htrivial, hdecomp, hcommute⟩
    exact ⟨mulMapIso htrivial hdecomp hcommute, fun h₁ h₂ => rfl⟩

/-
1.3 - Quotient Groups
-/

end Borcherds
