import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

inductive ZMul : Type
  | r : ℤ → ZMul
  deriving DecidableEq

namespace ZMul

private def mul : ZMul → ZMul → ZMul
  | r i, r j => r (i + j)

private def one : ZMul :=
  r 0

instance : Inhabited (ZMul) :=
  ⟨one⟩

private def inv : ZMul → ZMul
  | r i => r (-i)

/-- The group structure on `ZMul`.
-/
instance : Group (ZMul) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro ⟨ a ⟩
    exact congr_arg r (zero_add a)
  mul_one := by
    rintro ⟨ a ⟩
    · exact congr_arg r (add_zero a)
  inv := inv
  inv_mul_cancel := by
    rintro ⟨ a ⟩
    · exact congr_arg r (neg_add_cancel a)


@[simp]
theorem r_mul_r (i j : ℤ) : r i * r j = r (i + j) :=
  rfl

theorem r_one_pow (k : ℕ) : (r 1 : ZMul) ^ k = r k := by
  induction' k with k IH
  · rw [Nat.cast_zero]
    rfl
  · rw [pow_succ', IH, r_mul_r]
    congr 1
    norm_cast
    rw [Nat.one_add]

theorem inv_r_simp : (r i)⁻¹ = r (-i) := by
  rfl

@[simp]
theorem r_one_pow' (k : ℤ) : (r 1 : ZMul) ^ k = r k := by
  have d := le_or_lt 0 k
  cases' d with pos neg
  lift k to ℕ using pos
  simp
  exact r_one_pow k
  suffices : ((r (1: ℤ)) ^ k)⁻¹ = (r k)⁻¹
  have := congrArg Inv.inv this
  simp at this
  exact this
  let l := -k
  have k_eq_nl : k = -l := by exact Int.eq_neg_comm.mp rfl
  have l_pos : l ≥ 0 := by linarith
  rw [k_eq_nl]
  have : ∃ l' : ℤ, l' = l := by use l
  cases' this with l' lp_eq_l
  have : l' ≥ 0 := by
    exact?
  lift l' to ℕ using this
  simp
  rw [←lp_eq_l]
  simp [inv_r_simp]
  exact r_one_pow l'

@[simp]
theorem r_pow (k : ℤ) : ((r t) : ZMul) ^ k = r (t * k) := by
  sorry


def a : (ZMul) × (ZMul) := (r 1, r 2)
def b : (ZMul) × (ZMul) := (r 1, r 3)

#eval (a*b).fst
#eval (a*b).snd
