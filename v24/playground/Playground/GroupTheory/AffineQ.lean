import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

-- the function x ↦ mx + c
structure AffineQ : Type where
  m : ℚ
  c : ℚ
  m_ne_0 : m ≠ 0
  deriving DecidableEq

example : (1 : ℝ) ≠ 0 := by norm_num

def mul (a b : AffineQ): AffineQ :=
  .mk (a.m*b.m) (a.m*b.c + a.c) (mul_ne_zero a.m_ne_0 b.m_ne_0)

private def one : AffineQ :=
  .mk 1 0 (by norm_num)

theorem mul_times (a b : ℚ) : Mul.mul a b = a * b := by exact rfl

instance : One AffineQ :=
  ⟨⟨1, 0, (by norm_num)⟩⟩

def inv (g : AffineQ) : AffineQ :=
  .mk g.m⁻¹ (-g.c/g.m) (inv_ne_zero g.m_ne_0)

example (r : ℚ): 1 * r = r := by
  exact Rat.one_mul r

instance : Group AffineQ where
  mul := mul
  mul_assoc := by
    intro a b c
    simp [(· * ·), mul]
    ring_nf
    constructor
    repeat rw [mul_times]
    exact Rat.mul_assoc a.m b.m c.m
    repeat rw [mul_times]
    ring_nf
  one := one
  one_mul := by
    intro a
    simp [(· * ·), mul]
    cases' a with m c
    simp
    constructor
    apply Rat.one_mul
    have : AffineQ.c (1 : AffineQ) = 0 := by rfl

    rw [this]
    simp

    have : AffineQ.m (1 : AffineQ) = 1 := by rfl
    rw [this]
    rw [mul_times]
    simp
  mul_one := by
    intro a
    simp [(· * ·), mul]
    cases' a with m c
    simp
    constructor
    rw [one]
    apply Rat.mul_one
    have : AffineQ.c (1 : AffineQ) = 0 := by rfl

    rw [this]
    rw [mul_times]
    simp
  inv := inv
  inv_mul_cancel := by
    intro r
    simp [(· * ·), mul]
    have : (1 : AffineQ) = AffineQ.mk 1 0 (by norm_num):= by rfl
    rw [this]
    simp
    constructor
    rw [inv, mul_times]
    simp [r.3]
    rw [inv, mul_times]
    field_simp

theorem inv_eq (g : AffineQ) : g⁻¹ = AffineQ.mk g.m⁻¹ (-g.c/g.m) (inv_ne_zero g.m_ne_0) := by rfl

theorem mul_eq (a b : AffineQ) : a * b = .mk (a.m*b.m) (a.m*b.c + a.c) (mul_ne_zero a.m_ne_0 b.m_ne_0)
 := by rfl

def TranslatesZ : Subgroup AffineQ where
  carrier := { AffineQ.mk 1 i (by decide) | i : ℤ }
  mul_mem' := by
    rintro a b ⟨i1, a_def⟩ ⟨i2, b_def⟩
    use i1 + i2
    rw [←a_def, ←b_def]
    rw [mul_eq]
    simp
    exact Rat.add_comm ↑i1 ↑i2
  one_mem' := by
    use 0
    rfl
  inv_mem' := by
    intros x x_in_A
    cases' x_in_A with i hx
    use -i
    rw [inv_eq]
    simp
    constructor
    rw [← hx]
    rw [← hx]
    simp


def Translates2Z : Subgroup AffineQ where
  carrier := { AffineQ.mk 1 (2*i) (by decide) | i : ℤ }
  mul_mem' := by
    rintro a b ⟨i1, a_def⟩ ⟨i2, b_def⟩
    use i1 + i2
    rw [←a_def, ←b_def]
    rw [mul_eq]
    field_simp
    ring
  one_mem' := by
    use 0
    simp
    rfl
  inv_mem' := by
    intros x x_in_A
    cases' x_in_A with i hx
    use -i
    rw [inv_eq]
    simp
    constructor
    rw [← hx]
    rw [← hx]
    simp

def g := AffineQ.mk 2 0 (by decide)
def t := AffineQ.mk 1 1 (by decide)

open Pointwise

#eval (ConjAct.toConjAct g) • t

def C := (ConjAct.toConjAct g) • TranslatesZ

example : t ∈ TranslatesZ := by
  use 1
  decide

example : t ∉ C := by
  intro t_in_C
  cases' t_in_C with w h
  simp at h
  cases' h with w_in_tz g_act_w_is_t
  simp at g_act_w_is_t
  rw [ConjAct.toConjAct_smul] at g_act_w_is_t
  cases' w_in_tz with i hi
  have : g = AffineQ.mk 2 0 (by decide) := by decide
  rw [this] at g_act_w_is_t
  rw [← hi] at g_act_w_is_t
  simp [mul_eq, inv_eq] at g_act_w_is_t
  have : t = AffineQ.mk 1 1 (by decide) := by decide
  rw [this] at g_act_w_is_t
  simp at g_act_w_is_t
  norm_cast at g_act_w_is_t
  omega
