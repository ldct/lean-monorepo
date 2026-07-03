import Mathlib

set_option linter.style.longLine false

open Polynomial

namespace Chapter_7_3

/-
# Definition (homomorphism of nonunital rings)

A homomorphism of nonunital rings is a map from one nonunital ring to another that respects the additive and multiplicative structures.
-/

/-
Example 1, as a nonunital ring homomorphism
-/
def intToZMod2ₙ : ℤ →ₙ+* (ZMod 2) where
  toFun := fun n => n
  map_mul' x y := by norm_cast
  map_zero' := by norm_cast -- this is not part of D&F's definition but can be deduced from the other axioms
  map_add' x y := by norm_cast


/-
# Definition (homomorphism of rings)

A homomorphism of rings is a map from one ring to another that respects the additive and multiplicative structures,
-/


/-
Example 1, as a ring homomorphism
-/
def intToZMod2 : ℤ →+* (ZMod 2) where
  toFun := fun n => n
  map_one' := by norm_cast
  map_mul' x y := by norm_cast
  map_zero' := by norm_cast
  map_add' x y := by norm_cast

example : intToZMod2 6 = 0 := by decide

/-
Example 1, written more closely to the text
-/
def intToZMod2' : ℤ →+* (ZMod 2) where
  toFun := fun n => if Even n then 0 else 1
  map_one' := by norm_cast
  map_mul' x y := by
    simp
    grind
  map_zero' := by
    simp
  map_add' x y := by
    by_cases hx : Even x
    <;> by_cases hy : Even y
    <;> simp [hx, hy]
    <;> grind


/-
Example 3 (as a ring homomorphism)
-/
def evalAtZero : ℚ[X] →+* ℚ where
  toFun := fun p => p.eval 0
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

example : evalAtZero (X ^ 2 + 4) = 4 := by
  norm_num [evalAtZero]

example (p : ℚ[X]) : p*X ∈ RingHom.ker evalAtZero := by
  simp [evalAtZero]

noncomputable example : Ideal ℚ[X] := RingHom.ker evalAtZero

/-
# Proposition 5, 6, 7 - omitted
-/

/-
# Definition (ideal)

Let R be a nonunital ring. An ideal of R is a subset I of R that is closed under addition and left multiplication by elements of R.

Mathlib does not have this definition. Instead, it requires that R be a unital ring.
-/


/-
Example (not from book): the ideal of even numbers
-/
example : Ideal ℤ where
  carrier := { 2 * i | i : ℤ }
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    ring
  zero_mem' := by
    use 0
    norm_num
  smul_mem' c d hx := by
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨ n, rfl ⟩ := hx
    use c * n
    grind [Int.zsmul_eq_mul]

/-
# Example 1, page 243

Given a ring `R`, the ideal `⊤` is the ideal of all elements of `R`, and the ideal `⊥` is the trivial ideal {0} (containing only the zero element).

The notation comes from the lattice structure on ideals.
-/

example {R} [Ring R] : (⊤ : Ideal R).carrier = Set.univ := rfl
example {R} [Ring R] : (⊥ : Ideal R).carrier = {0} := rfl

example {R} [Ring R] : Ideal R where
  carrier := ⊤
  add_mem' ha hb := by simp
  zero_mem' := by simp
  smul_mem' := by simp

example {R} [Ring R] : Ideal R where
  carrier := {0}
  add_mem' ha hb := by grind
  zero_mem' := by simp
  smul_mem' := by simp

/-
# Example 2, the ideal nℤ ⊆ ℤ
-/
example (n : ℤ) : Ideal ℤ := Ideal.span { n }

/-
Example 2, more from scratch
-/
def Multiples (n : ℤ) : Ideal ℤ where
  carrier := { n * i | i : ℤ }
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    ring
  zero_mem' := by
    use 0
    norm_num
  smul_mem' c d hx := by
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨ n, rfl ⟩ := hx
    use c * n
    grind [Int.zsmul_eq_mul]

lemma multiples_1_eq_top : Multiples 1 = ⊤ := by
  ext i
  simp [Multiples]

example : Multiples 0 = ⊥ := by
  ext i
  simp [Multiples]

example : Multiples 2 = Multiples (-2) := by
  ext i
  simp only [Multiples, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, Int.reduceNeg, neg_mul]
  constructor
  · rintro ⟨ j, rfl ⟩
    use -j
    ring
  · rintro ⟨ j, rfl ⟩
    use -j
    ring

instance : CompleteLattice (Ideal ℤ) := by infer_instance
instance : SemilatticeSup (Submodule (Ideal ℤ) (Ideal ℤ)) := by infer_instance

example : (Multiples 2) + (Multiples 3) = (Multiples 2) ⊔ (Multiples 3) := by rw [Submodule.add_eq_sup]

/-
Sum of ideals, via Mathlib's definition
-/
example : (Multiples 2) + (Multiples 3) = (Multiples 1) := by
  simp only [Submodule.add_eq_sup]
  ext i
  -- By Bezout's identity, since gcd(2, 3) = 1, there exist integers x and y such that 2x + 3y = 1.
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, 2 * x + 3 * y = 1 := by
    exists 2, -1
  have h_mul : 2 * (x * i) + 3 * (y * i) = i := by
    linear_combination' hxy * i
  -- Since $2 * (x * i) + 3 * (y * i) = i$, we have $i \in nℤ 2 ⊔ nℤ 3$.
  have h_mem : i ∈ Multiples 2 ⊔ Multiples 3 := by
    exact h_mul ▸ Submodule.add_mem_sup ( ⟨ x * i, rfl ⟩ ) ( ⟨ y * i, rfl ⟩ )
  exact iff_of_true h_mem ( by exact ⟨ i, by ring ⟩ )

example (a : Ideal ℤ) : a ⊔ a = a := by order

example (a : Ideal ℤ) : a + a = a := by
  rw [Submodule.add_eq_sup]
  order

lemma add_carrier_eq (I J : Ideal ℤ)
: (I + J).carrier = { i + j | (i ∈ I) (j ∈ J) } := by
  simp only [Submodule.add_eq_sup, Submodule.carrier_eq_coe]
  ext r
  constructor
  · intro h
    simp only [Set.mem_setOf_eq]
    exact Submodule.mem_sup.mp h
  · intro h
    simp only [SetLike.mem_coe]
    obtain ⟨ i, hi, j, hj, rfl ⟩ := h
    exact Submodule.add_mem_sup hi hj

lemma mem_ideal (I : Ideal ℤ) (x : ℤ)
: x ∈ I ↔ x ∈ I.carrier := by rfl

lemma add_mem_iff' (I J : Ideal ℤ) (x : ℤ) (hx : x ∈ (I + J))
: ∃ i j, i ∈ I ∧ j ∈ J ∧ i + j = x := by
  rw [mem_ideal, add_carrier_eq] at hx
  grind

lemma add_mem_iff (I J : Ideal ℤ) (x : ℤ)
: x ∈ (I + J) ↔ ∃ i j, i ∈ I ∧ j ∈ J ∧ i + j = x := by
  constructor
  · intro h
    obtain ⟨ i, j, hi, hj, rfl ⟩ := add_mem_iff' I J x h
    grind
  intro h
  obtain ⟨ i, j, hi, hj, rfl ⟩ := h
  simp only [Submodule.add_eq_sup]
  exact Submodule.add_mem_sup hi hj


example : (Multiples 2) + (Multiples 3) = (Multiples 1) := by
  simp only [multiples_1_eq_top]
  ext x
  constructor
  · intro h
    exact trivial
  intro h1
  have := Int.gcd_eq_gcd_ab 2 3
  norm_num at this
  have := congr(x * $this)
  norm_num at this
  symm at this
  rw [mul_add] at this
  rw [add_mem_iff]
  use 2 * x * Int.gcdA 2 3
  have l : ∃ i, 2 * i = 2 * x * Int.gcdA 2 3 := by
    use x * Int.gcdA 2 3
    grind
  simp only [Multiples, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, ↓existsAndEq, true_and, l]
  clear l
  use x * Int.gcdB 2 3
  grind

#check Submodule.mul

#synth AddCommMagma (Ideal ℤ)


#synth SupSet (Ideal ℤ)

#check (Multiples 2) + (Multiples 2)

#synth Mul (Ideal ℤ)
#synth Ring (ℤ ⧸ Multiples 2)

#synth Ring (ℤ × ℤ )

/-
https://math.bu.edu/people/rpollack/Teach/542spring07/542hw5_solns.pdf
-/

-- 1c
example : (ℚ × ℚ) →+* ℚ where
  toFun := fun (x, y) => x
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

-- 1d
example : (ℝ → ℝ) →+* ℝ where
  toFun := fun f => f 1
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

-- 1f
example : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := fun z => !![z.re, z.im; -z.im, z.re]
  map_one' := by
    simp [Matrix.one_fin_two]
  map_mul' x y := by
    rw [Matrix.mul_fin_two]
    congr
    <;> rw [← Complex.re_add_im x, ← Complex.re_add_im y] <;> simp <;> norm_cast
    ring
  map_zero' := by
    simp [Matrix.eta_fin_two 0]
  map_add' x y := by
    simp
    norm_cast
    ring

-- 23
example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (a, b), map_one' := by simp, map_mul' x y := by simp ; rfl, map_zero' := by simp, map_add' x y := by simp ; rfl
}

example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (b, a), map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (b, 0), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (0, b), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (a, 0), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (0, a), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (0, 0), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (a, a), map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (b, b), map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

/-
# Definition (product of ideals)

In mathlib, ideals are defined as submodules
-/
open Pointwise in
theorem Ideal.mul_def {R : Type*} [Semiring R] (I J : Ideal R) :
    I * J = Ideal.span ((I : Set R) * (J : Set R)) := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr s hs
    exact Ideal.subset_span (Set.mul_mem_mul hr hs)
  · rw [Ideal.span_le]
    rintro x ⟨r, hr, s, hs, rfl⟩
    exact Ideal.mul_mem_mul hr hs

#synth Pow (Ideal ℤ) ℕ


-- Equivant ways to state that P is increasing
lemma increasing_iff (P : ℕ → ℕ)
: (∀ i, P i ≤ P (i + 1)) → (∀ i j, i < j → P i ≤ P j)
:= by
  intro h i j hij
  induction hij with
  | refl => exact h i
  | step hij' ih => exact le_trans ih (h _)


#check NonUnitalRing

#check Subring.toNonUnitalSubring

#check NonUnitalSubring

example {R} [Ring R] (I : Ideal R) (hI : (1 : R) ∈ I) : Subsemiring R where
  carrier := I.carrier
  mul_mem' _ hb := I.mul_mem_left _ hb
  add_mem' ha hb := I.add_mem ha hb
  zero_mem' := I.zero_mem
  one_mem' := hI

example {R} [Ring R] (I : Ideal R) : NonUnitalSubring R where
  carrier := I.carrier
  add_mem' ha hb := I.add_mem ha hb
  zero_mem' := I.zero_mem
  mul_mem' _ hb := I.mul_mem_left _ hb
  neg_mem' ha := I.neg_mem ha

/-
# Execises

In all the exercises, it is stated that R is a ring with identity 1≠0.
-/


/-
# Exercise 1
-/
def evenIdeal := Ideal.span {(2 : ℤ)}

abbrev evenNonUnitalRing := {x : ℤ // x ∈ Ideal.span {(2 : ℤ)}}
example : NonUnitalRing evenNonUnitalRing := inferInstance

abbrev divisibleBy3NonUnitalRing := {x : ℤ // x ∈ Ideal.span {(3 : ℤ)}}
example : NonUnitalRing divisibleBy3NonUnitalRing := inferInstance

example : IsEmpty (evenNonUnitalRing ≃+* divisibleBy3NonUnitalRing) := by
  rw [isEmpty_iff]
  intro φ
  have hmem2 : (2 : ℤ) ∈ evenIdeal := Ideal.mem_span_singleton.mpr (dvd_refl 2)
  let e : evenNonUnitalRing := ⟨2, hmem2⟩
  have hee : e * e = e + e := Subtype.ext (by norm_num)
  have he0 : e ≠ 0 := fun h => absurd (congr_arg Subtype.val h) (by norm_num)
  have hφeq : φ e * φ e = φ e + φ e := by rw [← map_mul, hee, map_add]
  have hφ0 : φ e ≠ 0 := fun h => he0 (φ.injective (h.trans (map_zero φ).symm))
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp (φ e).prop
  have hval : (φ e).val * (φ e).val = (φ e).val + (φ e).val := by exact_mod_cast hφeq
  rw [hk] at hval
  have h1 : 3 * k * (3 * k - 2) = 0 := by linear_combination hval
  rcases mul_eq_zero.mp h1 with h | h
  · exact hφ0 (Subtype.ext (by rw [hk]; omega))
  · omega

/-
# Exercise 4

Find all homomorphisms from ℤ to ℤ/30ℤ
-/

example : ℤ →ₙ+* ZMod 30 where
  toFun := fun _ => 0
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

-- The surjective homomorphism, reduction mod 30
def reductionMod30 : ℤ →ₙ+* ZMod 30 where
  toFun := fun i => i
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

example : reductionMod30 66 = 6 := by rfl

-- These are the only two homorphisms, since any homomorphism φ satisfies φ(1) = φ(1·1) = φ(1)² hence φ(1) ∈ 0, 1, and the homomorphism is completely determined by the value of φ(1).

/-
# A variation of exercise 4

Find all homomorphisms from ℤ to 30ℤ
-/

/-
# Exercise 5

Find all ring homomorphisms from ℤ × ℤ to ℤ.

We will consider two homomorphisms the same if they are equal as functions (`toFun`). We will use →ₙ+* and →+* depending on what additional properties they satisfy.
-/

example : ℤ × ℤ →ₙ+* ℤ := { toFun := fun (a, b) => 0, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp }
example : ℤ × ℤ →+* ℤ := { toFun := fun (a, b) => a, map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp }
example : ℤ × ℤ →+* ℤ := { toFun := fun (a, b) => b, map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp }

lemma sq_eq_self (a : ℤ) (h : a * a = a) : a = 0 ∨ a = 1 := by
  by_cases h0 : a = 0
  · grind
  right
  qify at *
  field_simp [h0] at h
  exact h

lemma my_lemma (h : ℤ × ℤ →ₙ+* ℤ) : h (1, 0) = 1 ∨ h (1, 0) = 0 := by
  have : h ((1, 0) * (1, 0)) = h (1, 0) * h (1, 0) := by
    exact MulHomClass.map_mul h (1, 0) (1, 0)
  rw [show ((1, 0) : (ℤ × ℤ)) * (1, 0) = (1, 0) by rfl] at this
  exact mul_left_eq_self₀.mp (id (Eq.symm this))

-- The three non-unital ring homs from ℤ × ℤ to ℤ
def hom_zero : ℤ × ℤ →ₙ+* ℤ where
  toFun := fun _ => 0
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

def hom_fst : ℤ × ℤ →ₙ+* ℤ where
  toFun := fun p => p.1
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

def hom_snd : ℤ × ℤ →ₙ+* ℤ where
  toFun := fun p => p.2
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

@[simp] lemma hom_zero_apply (p : ℤ × ℤ) : hom_zero p = 0 := rfl
@[simp] lemma hom_fst_apply (p : ℤ × ℤ) : hom_fst p = p.1 := rfl
@[simp] lemma hom_snd_apply (p : ℤ × ℤ) : hom_snd p = p.2 := rfl

-- Every non-unital ring hom from ℤ × ℤ to ℤ is determined by the images of (1,0) and (0,1)
lemma hom_formula (h : ℤ × ℤ →ₙ+* ℤ) (a b : ℤ) : h (a, b) = a * h (1, 0) + b * h (0, 1) := by
  have h1 : (a, b) = a • (1, 0) + b • (0, 1) := by ext <;> simp
  rw [h1, map_add, map_zsmul, map_zsmul]
  simp

lemma hom_01_sq (h : ℤ × ℤ →ₙ+* ℤ) : h (0, 1) = 0 ∨ h (0, 1) = 1 := by
  have : h ((0, 1) * (0, 1)) = h (0, 1) * h (0, 1) := MulHomClass.map_mul h (0, 1) (0, 1)
  rw [show ((0, 1) : ℤ × ℤ) * (0, 1) = (0, 1) from rfl] at this
  exact sq_eq_self _ (by linarith)

lemma hom_prod_zero (h : ℤ × ℤ →ₙ+* ℤ) : h (1, 0) * h (0, 1) = 0 := by
  have hmul : h ((1, 0) * (0, 1)) = h (1, 0) * h (0, 1) := MulHomClass.map_mul h (1, 0) (0, 1)
  have : ((1:ℤ),(0:ℤ)) * ((0:ℤ),(1:ℤ)) = (0 : ℤ × ℤ) := rfl
  rw [this, map_zero] at hmul
  linarith

-- Classification: every hom is one of the three
lemma hom_classification (h : ℤ × ℤ →ₙ+* ℤ) :
    h = hom_zero ∨ h = hom_fst ∨ h = hom_snd := by
  have h10 := my_lemma h
  have h01 := hom_01_sq h
  have hprod := hom_prod_zero h
  rcases h10 with h10eq | h10eq <;> rcases h01 with h01eq | h01eq
  · -- h(1,0) = 1, h(0,1) = 0 → fst projection
    right; left
    ext ⟨a, b⟩
    change h (a, b) = a
    rw [hom_formula h a b, h10eq, h01eq]; ring
  · -- h(1,0) = 1, h(0,1) = 1 → contradicts product = 0
    exfalso; rw [h10eq, h01eq] at hprod; simp at hprod
  · -- h(1,0) = 0, h(0,1) = 0 → zero map
    left
    ext ⟨a, b⟩
    change h (a, b) = 0
    rw [hom_formula h a b, h10eq, h01eq]; ring
  · -- h(1,0) = 0, h(0,1) = 1 → snd projection
    right; right
    ext ⟨a, b⟩
    change h (a, b) = b
    rw [hom_formula h a b, h10eq, h01eq]; ring

-- The three homs are distinct
lemma hom_zero_ne_fst : hom_zero ≠ hom_fst := by
  intro h; have := DFunLike.congr_fun h (1, 0); simp at this
lemma hom_zero_ne_snd : hom_zero ≠ hom_snd := by
  intro h; have := DFunLike.congr_fun h (0, 1); simp at this
lemma hom_fst_ne_snd : hom_fst ≠ hom_snd := by
  intro h; have := DFunLike.congr_fun h (1, 0); simp at this

open Classical in
noncomputable def homEquivFin3 : (ℤ × ℤ →ₙ+* ℤ) ≃ Fin 3 where
  toFun h :=
    if h = hom_zero then 0
    else if h = hom_fst then 1
    else 2
  invFun
    | 0 => hom_zero
    | 1 => hom_fst
    | 2 => hom_snd
  left_inv h := by
    rcases hom_classification h with rfl | rfl | rfl
    · simp
    · simp [hom_zero_ne_fst.symm]
    · simp [hom_zero_ne_snd.symm, hom_fst_ne_snd.symm]
  right_inv i := by
    fin_cases i
    · simp
    · simp [Ne.symm hom_zero_ne_fst]
    · simp [Ne.symm hom_zero_ne_snd, Ne.symm hom_fst_ne_snd]

example : Nat.card (ℤ × ℤ →ₙ+* ℤ) = 3 := by
  rw [Nat.card_congr homEquivFin3, Nat.card_fin]

/-
# Exercise 18, part 1
-/
example {R} [Ring R] (I J : Ideal R) : Ideal R where
  carrier := I ∩ J
  add_mem' := by
    rintro a b ⟨ ha, hb ⟩ ⟨ hc, hd ⟩
    simp at *
    grind [Ideal.add_mem]
  zero_mem' := by simp
  smul_mem' := by
    intro c x ⟨ ha, hb ⟩
    simp at *
    grind [Ideal.mul_mem_left]

/-
# Exercise 18, part 2
-/
example {R I} [Ring R] (P : I → Ideal R) : Ideal R where
  carrier := { x | ∀ i, x ∈ P i }
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    intro i
    grind [Ideal.add_mem]
  zero_mem' := by simp
  smul_mem' := by
    intro c x ha
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    intro i
    grind [Ideal.mul_mem_left]

/-
# Exercise 19

Note: the theorem is true for Semirings too, but we have weakened it
-/
example {R} [Ring R] (P : ℕ → (Ideal R)) (hP : ∀ i j, i ≤ j → P i ≤ P j)
: Ideal R where
  carrier := { x | ∃ i, x ∈ P i } -- todo change to bigoperator
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    obtain ⟨ i, ha ⟩ := ha
    obtain ⟨ j, hb ⟩ := hb
    use (max i j) + 1
    apply Ideal.add_mem
    · exact hP i (max i j + 1) (by grind) ha
    · exact hP j (max i j + 1) (by grind) hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    obtain ⟨ i, hx ⟩ := hx
    use i
    have := @(P i).smul_mem' c x (by simpa)
    simp_all


-- something something https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Asserting.20that.202.E2.84.A4.20forms.20a.20non-unital.20ring

example : CommRing (ℤ ⧸ Ideal.span {(2 : ℤ)}) := by infer_instance

-- example : NonUnitalRing (Ideal.span {(2 : ℤ)}).toNonUnitalSubring := by infer_instance

example (T : Type*) (R S : Set T) : Set S := { x | x.val ∈ R}

/-
# Exercise 20, part 1
-/
example {R} [Ring R] (I : Ideal R) (S : Subsemiring R) : Ideal S where
  carrier := { x | x.val ∈ I ∧ x.val ∈ S } -- note - x.val ∈ S will simplify to true
  add_mem' := by
    intro a b ha hb
    simp at *
    grind [Ideal.add_mem]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [SetLike.coe_mem, and_true, Set.mem_setOf_eq, smul_eq_mul, Subsemiring.coe_mul] at *
    exact Ideal.mul_mem_left I c hx

/-
# Exercise 20, part 2 - omitted
-/


end Chapter_7_3
