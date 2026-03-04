import Mathlib
import Playground.NormNumI
import Qq
open Lean Meta Qq

open Complex

theorem eq_sqrt_cases (x y : ℝ)
: y = Real.sqrt x ↔
  (y * y = x ∧ 0 ≤ y) ∨ (x < 0 ∧ y = 0) := by
  grind [Real.sqrt_eq_cases]

macro "norm_sqrt_eq" : tactic => `(tactic| rw [Real.sqrt_eq_cases] <;> ring_nf <;> repeat norm_num )
macro "norm_eq_sqrt" : tactic => `(tactic| rw [eq_sqrt_cases] <;> ring_nf <;> repeat norm_num )

-- Normalize square roots of rational literals
macro "norm_sqrt" : tactic => `(tactic| first | norm_sqrt_eq | norm_eq_sqrt)

example : Real.sqrt 25 = 5 := by norm_sqrt
example : Real.sqrt 4 = 2 := by norm_sqrt
example : Real.sqrt 18 = 3*Real.sqrt 2 := by norm_sqrt
example : 2 = Real.sqrt 4:= by norm_sqrt
example : Real.sqrt (1/4) = 1/2 := by norm_sqrt
example : Real.sqrt (1/2) = Real.sqrt 2 / 2 := by norm_sqrt


-- our aim is to reprove this from scratch
#check card_rootsOfUnity

def IsComplexNthRootOfUnity (n : ℕ) (a : ℂ) : Prop :=
  a ^ n = 1


example : (Real.sqrt 3)^2 = 3 := by norm_num

lemma IsComplexNthRootOfUnity_iff (n : ℕ) (a : ℂ) : IsComplexNthRootOfUnity n a ↔ a ^ n = 1 := by rfl

example : (Real.sqrt 3)^2 = 3 := by norm_num

example : (Real.sqrt 3)^2 = 3 := by simp

example : (Real.sqrt (3:ℝ))^2 = 3 := by grind [Real.sq_sqrt]

example (r : ℝ) (hr : 0 ≤ r) : (Real.sqrt r)^2 = r := by grind [Real.sq_sqrt]

example : (Real.sqrt 2)^4 = 4 := by
  have : (0 : ℝ) ≤ 2 := by norm_num
  grind [Real.sq_sqrt]

example : (Real.sqrt 2)^3 = 2*Real.sqrt 2 := by
  have : (0 : ℝ) ≤ 2 := by norm_num
  grind [Real.sq_sqrt]

example : (3 * I) = (3:ℝ) • I := by
  norm_num

example : 5 • I + 4 + 3 • I = 4 + 8 • I := by
  match_scalars
  <;> norm_num

lemma mul_I (r : ℝ) : r • I = r * I := by exact rfl

lemma mul_1 (r : ℝ) : r • (1 : ℂ) = r * 1 := by exact rfl

syntax "rep" tactic : tactic
macro_rules
  | `(tactic|rep $t) =>
  `(tactic|$t; $t; $t; $t)


example : 0 ≤ 4 := by
  rep (apply Nat.le.step)
  apply Nat.le.refl


theorem I_pow_4n_1 (n : ℕ) : I^(4*n + 1) = I := by
  rw [show I^(4*n + 1) = I^(4*n) * I by ring_nf]
  rw [show I^(4*n) = (I^4)^n by ring]
  simp

example : I^9 = I := by
  rw [show 9 = 4*2 + 1 by norm_num]
  rw [I_pow_4n_1]

macro "normI" : tactic => `(tactic|
  simp only [show I^2 = -1 by norm_num, show I^3 = -I by norm_num, show I^4 = 1 by norm_num])

example : I^5 = I^(4 + 1) := by rfl

def Ipow (n : ℕ) : ℂ :=
  I ^ n

def pi := 3

#check q([42 + 1])

#eval q(3)

lemma Ipow_mod_4 (n r: ℕ) : Ipow (4 * n + r) = I^r := by
  rw [Ipow, show I^(4 * n + r) = (I^4)^n * I^r by ring, I_pow_four, one_pow, one_mul]

lemma Ipow_4_times (n : ℕ) : Ipow (4 * n + 0) = 1 := by
  rw [Ipow, show I^(4 * n + 0) = (I^4)^n by ring, I_pow_four, one_pow]

lemma I_pow_eq_Ipow (n : ℕ) : I^n = Ipow n := by rfl

set_option trace.debug true

dsimproc_decl iPowCompute (Ipow _) := fun e => do
  let_expr Ipow m ← e | return .continue
  let some n := m.nat? | return .continue
  let l := n / 4
  return .done ((fun (a b c : ℕ) => q(Ipow ($a * $b + $c))) 4 l (n % 4))

example : I ^ 6 = -1 := by
  rw [I_pow_eq_Ipow]
  dsimp only [iPowCompute]
  rw [Ipow_mod_4]
  norm_num

example : I ^ 7 = -I := by
  rw [I_pow_eq_Ipow]
  dsimp only [iPowCompute]
  rw [Ipow_mod_4]
  norm_num

example : I ^ 8 = 1 := by
  rw [I_pow_eq_Ipow]
  dsimp only [iPowCompute]
  rw [Ipow_mod_4]
  norm_num



example : IsComplexNthRootOfUnity 3 ((-1/2 + 1/2 * √3 * I) : ℂ) := by
  rw [IsComplexNthRootOfUnity_iff]
  ring_nf
  normI
  rw [show ((√3 : ℂ) ^ 2) = 3 by norm_cast; norm_num]
  norm_num
  have :
    -(1 / 8) + √3 * I * (3 / 8) + 9 / 8 + -(√3 ^ 3 * I * (1 / 8))
     = 8 / 8 + (3 * √3 / 8 + -(√3 ^ 3 / 8)) * I := by ring
  rw [this]

  norm_cast
  rw [show (8 : ℂ) / 8 = ((8 / 8) : ℝ) * 1 by norm_num]

  rw [← mul_I]
  rw [← mul_1]

  match_scalars
  · norm_num
  · have : (0 : ℝ) ≤ 3 := by norm_num
    grind [Real.sq_sqrt]
