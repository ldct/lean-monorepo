import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Analysis.Normed.Field.Lemmas

/-
# Key definitions

- AffineQ: the type of functions x : ℚ ↦ mx + c, represented as explicit (m, c)
- TranslatesZ, Translates2Z : the translations by integers and even integers respectively

# Key theorems



-/
-- the function x ↦ mx + c

structure AffineQ : Type where
  m : ℚ
  c : ℚ
  m_nz : m ≠ 0
deriving DecidableEq

instance : Mul AffineQ where
  mul a b := ⟨ (a.m*b.m), (a.m*b.c + a.c), (mul_ne_zero a.m_nz b.m_nz) ⟩

@[grind =]
theorem mul_eq (a b : AffineQ) : a * b = ⟨ (a.m*b.m), (a.m*b.c + a.c), (mul_ne_zero a.m_nz b.m_nz) ⟩ := rfl

instance : One AffineQ := ⟨⟨1, 0, (by norm_num)⟩⟩

@[grind =]
lemma one_eq : (1 : AffineQ) = ⟨1, 0, (by norm_num)⟩ := rfl

instance : Inv AffineQ where
  inv g := .mk g.m⁻¹ (-g.c/g.m) (inv_ne_zero g.m_nz)

lemma inv_eq (g : AffineQ) : g⁻¹ = .mk g.m⁻¹ (-g.c/g.m) (inv_ne_zero g.m_nz) := rfl

example (r : ℚ) : 1 * r = r := by
  exact Rat.one_mul r

instance : Group AffineQ := Group.ofLeftAxioms
  (by
    grind
  ) (by
    rintro ⟨ m, c, _ ⟩
    grind
  ) (by
    grind [inv_eq]
  )

def TranslatesZ : Subgroup AffineQ where
  carrier := { ⟨ 1, i, (by decide) ⟩ | i : ℤ }
  mul_mem' := by
    rintro a b ⟨i1, rfl⟩ ⟨i2, rfl⟩
    use i1 + i2
    grind
  one_mem' := by
    use 0
    rfl
  inv_mem' := by
    rintro x ⟨i, hx⟩
    use -i
    grind [one_eq_inv, inv_eq]

def Translates2Z : Subgroup AffineQ where
  carrier := { ⟨ 1, 2*i, (by decide) ⟩ | i : ℤ }
  mul_mem' := by
    rintro a b ⟨i1, rfl⟩ ⟨i2, rfl⟩
    use i1 + i2
    grind
  one_mem' := by
    use 0
    simp
    rfl
  inv_mem' := by
    rintro x ⟨i, hx⟩
    use -i
    grind [one_eq_inv, inv_eq]

def g := AffineQ.mk 2 0 (by decide)
def t := AffineQ.mk 1 1 (by decide)

open Pointwise

#eval! (ConjAct.toConjAct g) • t

def C := (ConjAct.toConjAct g) • TranslatesZ

lemma t_in_lhs : t ∈ TranslatesZ := by
  use 1
  decide

lemma t_not_in_rhs : t ∉ C := by
  rintro ⟨w, ⟨ i, hi ⟩ , g_act_w_is_t⟩
  have g_act_w_is_t : ConjAct.toConjAct g • w = t := by simp_all
  rw [ConjAct.toConjAct_smul] at g_act_w_is_t
  have : g = AffineQ.mk 2 0 (by decide) := by decide
  rw [this] at g_act_w_is_t
  rw [← hi] at g_act_w_is_t
  simp only [mul_eq, mul_one, add_zero, inv_eq, neg_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_inv_cancel₀, mul_zero, zero_add] at g_act_w_is_t
  have : t = AffineQ.mk 1 1 (by decide) := by decide
  rw [this] at g_act_w_is_t
  simp at g_act_w_is_t
  norm_cast at g_act_w_is_t
  grind
