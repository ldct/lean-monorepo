import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

inductive ZMul : Type
  | r : ℤ → ZMul
  deriving DecidableEq

namespace ZMul

def myMul : ZMul → ZMul → ZMul
  | r i, r j => r (i + j)

def one : ZMul := r 0

instance : Inhabited (ZMul) :=
  ⟨one⟩

def inv : ZMul → ZMul
  | r i => r (-i)

instance : Group (ZMul) where
  mul := myMul
  mul_assoc := by rintro (a | a) (b | b) (c | c)
    <;> simp only [(· * ·)]
    <;> grind [myMul]
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


instance : CommGroup (ZMul) where
  mul_comm a b := by
    obtain ⟨ a, rfl ⟩ := (show ∃ a', r a' = a by exact exists_apply_eq_apply r a.1)
    obtain ⟨ b, rfl ⟩ := (show ∃ b', r b' = b by exact exists_apply_eq_apply r b.1)
    grind [r_mul_r]

theorem r_one_pow (k : ℕ) : (r 1 : ZMul) ^ k = r k := by
  induction k
  case zero =>
    rw [Nat.cast_zero]
    rfl
  case succ n IH =>
  · rw [pow_succ', IH]
    grind [r_mul_r]

theorem inv_r_simp (i : ℤ) : (r i)⁻¹ = r (-i) := by
  rfl

@[simp]
theorem r_one_pow' (k : ℤ) : (r 1 : ZMul) ^ k = r k := by
  have d := le_or_gt 0 k
  obtain pos | neg := d
  · lift k to ℕ using pos
    simp
    exact r_one_pow k

  suffices : ((r (1: ℤ)) ^ k)⁻¹ = (r k)⁻¹
  · have := congrArg Inv.inv this
    simp at this
    exact this
  let l := -k
  have k_eq_nl : k = -l := by exact Int.eq_neg_comm.mp rfl
  have l_pos : l ≥ 0 := by linarith
  rw [k_eq_nl]
  have : ∃ l' : ℤ, l' = l := by use l
  cases' this with l' lp_eq_l
  have : l' ≥ 0 := by
    exact le_of_le_of_eq l_pos (id (Eq.symm lp_eq_l))
  lift l' to ℕ using this
  simp
  rw [←lp_eq_l]
  simp [inv_r_simp]
  exact r_one_pow l'

example {G} [CommGroup G] (a b : G) (k : ℤ)
: (a * b)^k = a^k * b^k := by exact mul_zpow a b k

theorem r1_npow (k : ℕ) : (r 1) ^ k = r k := by
  induction k
  case zero => rfl
  case succ n IH =>
    rw [pow_add, IH, show (r 1)^1 = (r 1) by group, r_mul_r]
    grind

@[simp]
theorem r_npow (t : ℕ) (k : ℕ) : (r t) ^ k = r (t * k) := by
  induction t
  case zero =>
    norm_cast
    have : r 0 = 1 := by rfl
    rw [this]
    simp
    exact this
  case succ t IH =>
    have : r (t + 1) = (r t) * (r 1) := by
      rw [r_mul_r]
    norm_cast at this
    rw [this, mul_pow, IH, r1_npow, r_mul_r]
    grind

theorem rz_zpow (t k : ℤ) : (r t) ^ k = r (t * k) := by
  sorry

def a : (ZMul) × (ZMul) := (r 1, r 2)
def b : (ZMul) × (ZMul) := (r 1, r 3)

#eval (a*b).fst
#eval (a*b).snd

example : CommGroup ZMul where
  mul_comm := by
    intro ⟨i⟩ ⟨j⟩
    simp only [r_mul_r, r.injEq]
    exact Int.add_comm i j

example : AddCommGroup ℤ where
  add_comm := by
    intro a b
    exact AddCommMagma.add_comm a b
