import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

/-- Every natural number is less than its successor. -/
theorem succ_gt (n : ℕ) : n < n + 1 := by omega

/-- 2 is prime. -/
example : Nat.Prime 2 := by decide

#check Nat.Prime
#eval (List.range 20).filter Nat.Prime
