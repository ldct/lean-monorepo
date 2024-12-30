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

-- have (m c m' c' : ℚ) : AffineQ.mk m c _ = AffineQ.mk m' c' _ ↔

-- m'(mx + c) + c' = m'm x + m'c + c'
def mul2 (a b : AffineQ): AffineQ :=
  .mk (a.m*b.m) (a.m*b.c + a.c) (mul_ne_zero a.m_ne_0 b.m_ne_0)

private def one : AffineQ :=
  .mk 1 0 (by norm_num)

theorem mul_times (a b : ℚ) : Mul.mul a b = a * b := by exact rfl

instance : One AffineQ :=
  ⟨⟨1, 0, (by norm_num)⟩⟩


def inv (g : AffineQ) : AffineQ :=
  .mk g.m⁻¹ (g.c/g.m) (inv_ne_zero g.m_ne_0)

example (r : ℚ): 1 * r = r := by
  exact Rat.one_mul r
instance : Group AffineQ where
  mul := mul2
  mul_assoc := by
    intro a b c
    simp [(· * ·), mul2]
    ring_nf
    constructor
    repeat rw [mul_times]
    exact Rat.mul_assoc a.m b.m c.m
    repeat rw [mul_times]
    ring_nf
  one := one
  one_mul := by
    intro a
    simp [(· * ·), mul2]
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
    simp [(· * ·), mul2]
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
    simp [(· * ·), mul2]
    suggest_tactics
