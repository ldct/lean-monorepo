import Mathlib

namespace FiniteGroup

/-
Definition 1.2 - Abstract Group
-/
class Group (G : Type*) [DecidableEq G] extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

attribute [simp] Group.one_mul Group.mul_one Group.inv_mul_cancel Group.mul_inv_cancel

structure BSubgroup (G : Type*) [DecidableEq G] [Group G] where
  carrier : Finset G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  inv_mem : ∀ x : G, x ∈ carrier → x⁻¹ ∈ carrier

variable {G : Type*} [DecidableEq G] [Group G]

/-! ## Derived group operations -/

lemma Group.mul_left_cancel_iff (a b c : G) : a * b = a * c ↔ b = c := by
  constructor
  · intro h
    have h' := congrArg (fun x => a⁻¹ * x) h
    simpa only [← Group.mul_assoc, Group.inv_mul_cancel, Group.one_mul] using h'
  · exact congrArg (fun x => a * x)

lemma Group.mul_right_cancel_iff (a b c : G) : a * b = c * b ↔ a = c := by
  constructor
  · intro h
    have h' := congrArg (fun x => x * b⁻¹) h
    simpa only [Group.mul_assoc, Group.mul_inv_cancel, Group.mul_one] using h'
  · exact fun h => congrArg (fun x => x * b) h

lemma Group.mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c :=
  (Group.mul_left_cancel_iff a b c).mp h

lemma Group.mul_right_cancel {a b c : G} (h : a * b = c * b) : a = c :=
  (Group.mul_right_cancel_iff a b c).mp h

lemma Group.mul_left_injective (a : G) : Function.Injective (fun x : G => a * x) :=
  fun _ _ => Group.mul_left_cancel

lemma Group.mul_right_injective (a : G) : Function.Injective (fun x : G => x * a) :=
  fun _ _ => Group.mul_right_cancel

lemma Group.inv_inv (a : G) : a⁻¹⁻¹ = a := by
  apply Group.mul_right_cancel (b := a⁻¹)
  simp only [Group.inv_mul_cancel, Group.mul_inv_cancel]

lemma Group.inv_one : (1 : G)⁻¹ = 1 := by
  calc
    (1 : G)⁻¹ = 1⁻¹ * 1 := (Group.mul_one _).symm
    _ = 1 := Group.inv_mul_cancel _

lemma Group.mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b)⁻¹ * (a * b) = (b⁻¹ * a⁻¹) * (a * b) := by
    rw [Group.inv_mul_cancel]
    symm
    calc
      (b⁻¹ * a⁻¹) * (a * b) = b⁻¹ * (a⁻¹ * (a * b)) := Group.mul_assoc _ _ _
      _ = b⁻¹ * ((a⁻¹ * a) * b) :=
        congrArg (fun x => b⁻¹ * x) (Group.mul_assoc a⁻¹ a b).symm
      _ = b⁻¹ * (1 * b) := by rw [Group.inv_mul_cancel]
      _ = b⁻¹ * b := by rw [Group.one_mul]
      _ = 1 := Group.inv_mul_cancel _
  exact Group.mul_right_cancel h

/-! ## Left cosets -/

def lcoset (g : G) (H : BSubgroup G) : Finset G :=
  H.carrier.image (fun h => g * h)

lemma mem_lcoset {g x : G} {H : BSubgroup G} :
    x ∈ lcoset g H ↔ ∃ h ∈ H.carrier, g * h = x := by
  simp only [lcoset, Finset.mem_image]

lemma mem_lcoset_self (g : G) (H : BSubgroup G) : g ∈ lcoset g H :=
  mem_lcoset.mpr ⟨1, H.one_mem, Group.mul_one g⟩

lemma card_lcoset (g : G) (H : BSubgroup G) : (lcoset g H).card = H.carrier.card :=
  Finset.card_image_of_injective _ (Group.mul_left_injective g)

structure LeftCoset (H : BSubgroup G) where
  carrier : Finset G
  is_coset : ∃ g, carrier = lcoset g H

namespace LeftCoset

def of (g : G) (H : BSubgroup G) : LeftCoset H :=
  ⟨lcoset g H, ⟨g, rfl⟩⟩

@[ext] theorem ext {H : BSubgroup G} {C D : LeftCoset H}
    (h : C.carrier = D.carrier) : C = D := by
  cases C
  cases D
  cases h
  rfl

instance (H : BSubgroup G) : DecidableEq (LeftCoset H) := fun C D =>
  if h : C.carrier = D.carrier then isTrue (LeftCoset.ext h)
  else isFalse fun hCD => h (congrArg LeftCoset.carrier hCD)

unsafe instance (H : BSubgroup G) [Repr G] : Repr (LeftCoset H) where
  reprPrec C n := reprPrec C.carrier n

instance {H : BSubgroup G} : HMul G (LeftCoset H) (LeftCoset H) where
  hMul g C :=
    { carrier := C.carrier.image (fun x => g * x)
      is_coset := by
        obtain ⟨a, ha⟩ := C.is_coset
        refine ⟨g * a, ?_⟩
        rw [ha, lcoset, Finset.image_image]
        apply Finset.image_congr
        intro x _
        exact (Group.mul_assoc g a x).symm }

lemma hMul_of (g a : G) (H : BSubgroup G) :
    g * LeftCoset.of a H = LeftCoset.of (g * a) H := by
  apply LeftCoset.ext
  change (lcoset a H).image (fun x => g * x) = lcoset (g * a) H
  rw [lcoset, Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact (Group.mul_assoc g a x).symm

lemma card_carrier {H : BSubgroup G} (C : LeftCoset H) : C.carrier.card = H.carrier.card := by
  obtain ⟨g, hg⟩ := C.is_coset
  rw [hg, card_lcoset]

end LeftCoset

lemma lcoset_eq_iff (g k : G) (H : BSubgroup G) :
    lcoset g H = lcoset k H ↔ g⁻¹ * k ∈ H.carrier := by
  constructor
  · intro h
    have hk : k ∈ lcoset g H := by
      rw [h]
      exact mem_lcoset_self k H
    obtain ⟨x, hx, hkx⟩ := mem_lcoset.mp hk
    rw [← hkx, ← Group.mul_assoc, Group.inv_mul_cancel, Group.one_mul]
    exact hx
  · intro hq
    let q := g⁻¹ * k
    have hk : k = g * q := by
      calc
        k = 1 * k := (Group.one_mul k).symm
        _ = (g * g⁻¹) * k := by rw [Group.mul_inv_cancel]
        _ = g * (g⁻¹ * k) := Group.mul_assoc _ _ _
        _ = g * q := rfl
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨h, hh, hxh⟩ := mem_lcoset.mp hx
      apply mem_lcoset.mpr
      refine ⟨q⁻¹ * h, H.mul_mem _ _ (H.inv_mem _ hq) hh, ?_⟩
      calc
        k * (q⁻¹ * h) = (g * q) * (q⁻¹ * h) := by rw [hk]
        _ = g * (q * (q⁻¹ * h)) := Group.mul_assoc _ _ _
        _ = g * ((q * q⁻¹) * h) :=
          congrArg (fun x => g * x) (Group.mul_assoc q q⁻¹ h).symm
        _ = g * (1 * h) := by rw [Group.mul_inv_cancel]
        _ = g * h := by rw [Group.one_mul]
        _ = x := hxh
    · intro hx
      obtain ⟨h, hh, hxh⟩ := mem_lcoset.mp hx
      apply mem_lcoset.mpr
      refine ⟨q * h, H.mul_mem _ _ hq hh, ?_⟩
      calc
        g * (q * h) = (g * q) * h := (Group.mul_assoc _ _ _).symm
        _ = k * h := by rw [← hk]
        _ = x := hxh

lemma lcoset_disjoint_or_eq (g k : G) (H : BSubgroup G) :
    Disjoint (lcoset g H) (lcoset k H) ∨ lcoset g H = lcoset k H := by
  by_cases hEq : lcoset g H = lcoset k H
  · exact Or.inr hEq
  · left
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, hax⟩ := mem_lcoset.mp hx
    obtain ⟨b, hb, hbx⟩ := mem_lcoset.mp hx'
    have hkb : k * b = g * a := hbx.trans hax.symm
    have hmem : g⁻¹ * k = a * b⁻¹ := by
      calc
        g⁻¹ * k = (g⁻¹ * k) * 1 := (Group.mul_one _).symm
        _ = (g⁻¹ * k) * (b * b⁻¹) := by rw [Group.mul_inv_cancel]
        _ = ((g⁻¹ * k) * b) * b⁻¹ := (Group.mul_assoc _ _ _).symm
        _ = (g⁻¹ * (k * b)) * b⁻¹ :=
          congrArg (fun z => z * b⁻¹) (Group.mul_assoc g⁻¹ k b)
        _ = (g⁻¹ * (g * a)) * b⁻¹ := by rw [hkb]
        _ = ((g⁻¹ * g) * a) * b⁻¹ := by rw [← Group.mul_assoc]
        _ = (1 * a) * b⁻¹ := by rw [Group.inv_mul_cancel]
        _ = a * b⁻¹ := by rw [Group.one_mul]
    apply hEq
    apply (lcoset_eq_iff g k H).mpr
    rw [hmem]
    exact H.mul_mem _ _ ha (H.inv_mem _ hb)

lemma LeftCoset.of_eq_iff (g k : G) (H : BSubgroup G) :
    LeftCoset.of g H = LeftCoset.of k H ↔ g⁻¹ * k ∈ H.carrier := by
  constructor
  · intro h
    apply (lcoset_eq_iff g k H).mp
    exact congrArg LeftCoset.carrier h
  · intro h
    apply LeftCoset.ext
    exact (lcoset_eq_iff g k H).mpr h

/-! ## Lagrange's theorem -/

def leftCosets [Fintype G] (H : BSubgroup G) : Finset (LeftCoset H) :=
  Finset.univ.image fun g => LeftCoset.of g H

lemma mem_leftCosets [Fintype G] (g : G) (H : BSubgroup G) :
    LeftCoset.of g H ∈ leftCosets H :=
  Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

lemma leftCosets_biUnion [Fintype G] (H : BSubgroup G) :
    (leftCosets H).biUnion LeftCoset.carrier = Finset.univ := by
  apply Finset.ext
  intro g
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    exact Finset.mem_biUnion.mpr
      ⟨LeftCoset.of g H, mem_leftCosets g H, mem_lcoset_self g H⟩

lemma leftCosets_pairwiseDisjoint [Fintype G] (H : BSubgroup G) :
    (↑(leftCosets H) : Set (LeftCoset H)).PairwiseDisjoint LeftCoset.carrier := by
  intro C hC D hD hCD
  obtain ⟨c, hc⟩ := C.is_coset
  obtain ⟨d, hd⟩ := D.is_coset
  change Disjoint C.carrier D.carrier
  rw [hc, hd]
  rcases lcoset_disjoint_or_eq c d H with h | h
  · exact h
  · exfalso
    apply hCD
    apply LeftCoset.ext
    exact hc.trans (h.trans hd.symm)

lemma card_lagrange [Fintype G] (H : BSubgroup G) :
    Fintype.card G = H.carrier.card * (leftCosets H).card := by
  calc
    Fintype.card G = Finset.univ.card := Finset.card_univ.symm
    _ = ((leftCosets H).biUnion LeftCoset.carrier).card := by
      rw [leftCosets_biUnion]
    _ = ∑ C ∈ leftCosets H, C.carrier.card :=
      Finset.card_biUnion (leftCosets_pairwiseDisjoint H)
    _ = (leftCosets H).card * H.carrier.card :=
      Finset.sum_const_nat fun C _ => LeftCoset.card_carrier C
    _ = H.carrier.card * (leftCosets H).card := Nat.mul_comm _ _

lemma card_subgroup_dvd_card [Fintype G] (H : BSubgroup G) :
    H.carrier.card ∣ Fintype.card G := by
  refine ⟨(leftCosets H).card, ?_⟩
  exact card_lagrange H

/-! ## Normal subgroups and quotient groups -/

def rcoset (g : G) (H : BSubgroup G) : Finset G :=
  H.carrier.image fun h => h * g

lemma mem_rcoset {g x : G} {H : BSubgroup G} :
    x ∈ rcoset g H ↔ ∃ h ∈ H.carrier, h * g = x := by
  simp only [rcoset, Finset.mem_image]

def IsNormal (H : BSubgroup G) : Prop := ∀ g, lcoset g H = rcoset g H

namespace LeftCoset

variable {H : BSubgroup G}

lemma mul_lcoset_eq (hN : IsNormal H) (a b : G) :
    (lcoset a H ×ˢ lcoset b H).image (fun p : G × G => p.1 * p.2) = lcoset (a * b) H := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨u, v⟩, huv, huvx⟩ := Finset.mem_image.mp hx
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨p, hp, hau⟩ := mem_lcoset.mp hu
    obtain ⟨q, hq, hbv⟩ := mem_lcoset.mp hv
    have hpb : p * b ∈ lcoset b H := by
      rw [hN b]
      exact mem_rcoset.mpr ⟨p, hp, rfl⟩
    obtain ⟨r, hr, hbr⟩ := mem_lcoset.mp hpb
    apply mem_lcoset.mpr
    refine ⟨r * q, H.mul_mem _ _ hr hq, ?_⟩
    calc
      (a * b) * (r * q) = a * (b * (r * q)) := Group.mul_assoc _ _ _
      _ = a * ((b * r) * q) :=
        congrArg (fun x => a * x) (Group.mul_assoc b r q).symm
      _ = a * ((p * b) * q) := by rw [hbr]
      _ = a * (p * (b * q)) := by rw [Group.mul_assoc]
      _ = (a * p) * (b * q) := (Group.mul_assoc _ _ _).symm
      _ = u * v := by rw [hau, hbv]
      _ = x := huvx
  · intro hx
    obtain ⟨h, hh, habh⟩ := mem_lcoset.mp hx
    apply Finset.mem_image.mpr
    refine ⟨(a, b * h), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      exact ⟨mem_lcoset_self a H, mem_lcoset.mpr ⟨h, hh, rfl⟩⟩
    · exact (Group.mul_assoc a b h).symm.trans habh

def mul (hN : IsNormal H) (C D : LeftCoset H) : LeftCoset H :=
  { carrier := (C.carrier ×ˢ D.carrier).image fun p : G × G => p.1 * p.2
    is_coset := by
      obtain ⟨a, ha⟩ := C.is_coset
      obtain ⟨b, hb⟩ := D.is_coset
      refine ⟨a * b, ?_⟩
      rw [ha, hb]
      exact mul_lcoset_eq hN a b }

instance [Fact (IsNormal H)] : Mul (LeftCoset H) where
  mul := LeftCoset.mul Fact.out

lemma mul_of [Fact (IsNormal H)] (a b : G) :
    LeftCoset.of a H * LeftCoset.of b H = LeftCoset.of (a * b) H := by
  apply LeftCoset.ext
  change (lcoset a H ×ˢ lcoset b H).image (fun p : G × G => p.1 * p.2) = lcoset (a * b) H
  exact mul_lcoset_eq Fact.out a b

lemma inv_lcoset_eq (hN : IsNormal H) (a : G) :
    (lcoset a H).image Inv.inv = lcoset a⁻¹ H := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, hau⟩ := mem_lcoset.mp hu
    have hpa : p⁻¹ * a⁻¹ ∈ lcoset a⁻¹ H := by
      rw [hN a⁻¹]
      exact mem_rcoset.mpr ⟨p⁻¹, H.inv_mem _ hp, rfl⟩
    obtain ⟨r, hr, har⟩ := mem_lcoset.mp hpa
    apply mem_lcoset.mpr
    refine ⟨r, hr, ?_⟩
    calc
      a⁻¹ * r = p⁻¹ * a⁻¹ := har
      _ = (a * p)⁻¹ := (Group.mul_inv_rev a p).symm
      _ = u⁻¹ := by rw [hau]
      _ = x := hux
  · intro hx
    obtain ⟨h, hh, hah⟩ := mem_lcoset.mp hx
    have hright : a⁻¹ * h ∈ rcoset a⁻¹ H := by
      rw [← hN a⁻¹]
      exact mem_lcoset.mpr ⟨h, hh, rfl⟩
    obtain ⟨q, hq, hqa⟩ := mem_rcoset.mp hright
    apply Finset.mem_image.mpr
    refine ⟨a * q⁻¹, mem_lcoset.mpr ⟨q⁻¹, H.inv_mem _ hq, rfl⟩, ?_⟩
    calc
      (a * q⁻¹)⁻¹ = q⁻¹⁻¹ * a⁻¹ := Group.mul_inv_rev _ _
      _ = q * a⁻¹ := by rw [Group.inv_inv]
      _ = a⁻¹ * h := hqa
      _ = x := hah

def inv (hN : IsNormal H) (C : LeftCoset H) : LeftCoset H :=
  { carrier := C.carrier.image Inv.inv
    is_coset := by
      obtain ⟨a, ha⟩ := C.is_coset
      refine ⟨a⁻¹, ?_⟩
      rw [ha]
      exact inv_lcoset_eq hN a }

instance [Fact (IsNormal H)] : Inv (LeftCoset H) where
  inv := LeftCoset.inv Fact.out

lemma inv_of [Fact (IsNormal H)] (a : G) :
    (LeftCoset.of a H)⁻¹ = LeftCoset.of a⁻¹ H := by
  apply LeftCoset.ext
  change (lcoset a H).image Inv.inv = lcoset a⁻¹ H
  exact inv_lcoset_eq Fact.out a

instance : One (LeftCoset H) where
  one := LeftCoset.of 1 H

instance [Fact (IsNormal H)] : Group (LeftCoset H) where
  mul_assoc C D E := by
    obtain ⟨a, ha⟩ := C.is_coset
    obtain ⟨b, hb⟩ := D.is_coset
    obtain ⟨c, hc⟩ := E.is_coset
    have hC : C = LeftCoset.of a H := LeftCoset.ext ha
    have hD : D = LeftCoset.of b H := LeftCoset.ext hb
    have hE : E = LeftCoset.of c H := LeftCoset.ext hc
    rw [hC, hD, hE, mul_of, mul_of, mul_of, mul_of]
    exact congrArg (fun x => LeftCoset.of x H) (Group.mul_assoc a b c)
  one_mul C := by
    obtain ⟨a, ha⟩ := C.is_coset
    have hC : C = LeftCoset.of a H := LeftCoset.ext ha
    rw [hC]
    change LeftCoset.of (1 : G) H * LeftCoset.of a H = LeftCoset.of a H
    rw [mul_of]
    exact congrArg (fun x => LeftCoset.of x H) (Group.one_mul a)
  mul_one C := by
    obtain ⟨a, ha⟩ := C.is_coset
    have hC : C = LeftCoset.of a H := LeftCoset.ext ha
    rw [hC]
    change LeftCoset.of a H * LeftCoset.of (1 : G) H = LeftCoset.of a H
    rw [mul_of]
    exact congrArg (fun x => LeftCoset.of x H) (Group.mul_one a)
  inv_mul_cancel C := by
    obtain ⟨a, ha⟩ := C.is_coset
    have hC : C = LeftCoset.of a H := LeftCoset.ext ha
    rw [hC, inv_of, mul_of]
    exact congrArg (fun x => LeftCoset.of x H) (Group.inv_mul_cancel a)
  mul_inv_cancel C := by
    obtain ⟨a, ha⟩ := C.is_coset
    have hC : C = LeftCoset.of a H := LeftCoset.ext ha
    rw [hC, inv_of, mul_of]
    exact congrArg (fun x => LeftCoset.of x H) (Group.mul_inv_cancel a)

end LeftCoset

/-! ## A computable example -/

namespace Examples

@[ext] structure C4 where
  val : Fin 4
  deriving DecidableEq, Repr, Fintype

namespace C4

instance : Mul C4 where
  mul a b := ⟨a.val + b.val⟩

instance : One C4 where
  one := ⟨0⟩

instance : Inv C4 where
  inv a := ⟨-a.val⟩

instance : Group C4 where
  mul_assoc := by native_decide
  one_mul := by native_decide
  mul_one := by native_decide
  inv_mul_cancel := by native_decide
  mul_inv_cancel := by native_decide

def even : BSubgroup C4 where
  carrier := ({⟨0⟩, ⟨2⟩} : Finset C4)
  one_mem := by native_decide
  mul_mem := by native_decide
  inv_mem := by native_decide

theorem even_normal : IsNormal even := by
  intro g
  fin_cases g <;> native_decide

instance : Fact (IsNormal even) := ⟨even_normal⟩

#eval (⟨1⟩ : C4) * LeftCoset.of ⟨0⟩ even
#eval LeftCoset.of ⟨1⟩ even * LeftCoset.of ⟨1⟩ even

end C4
end Examples

end FiniteGroup
