import Mathlib

@[reducible]
def padWithO (n : Nat) (s : String) : String :=
  if s.length ≥ n then
    s
  else
    padWithO n ("o" ++ s)
termination_by n - s.length
decreasing_by
  have : "o".length = 1 := by rfl
  grind [String.length_append]

#eval padWithO 5 "abc"

example : padWithO 5 "abc" = "ooabc" := by
  unfold padWithO
  simp
  rw [show "abc".length = 3 by rfl]
  simp
  unfold padWithO
  simp
  rw [show "oabc".length = 4 by rfl]
  simp
  unfold padWithO
  rw [show "ooabc".length = 5 by rfl]
  simp

theorem h_pad_length (n : ℕ) (s : String) : (padWithO n s).length = max n s.length := by
  induction' h : n - s.length using Nat.strong_induction_on with n ih generalizing s;
  unfold padWithO
  subst h
  simp_all only [ge_iff_le]
  split
  next h => grind
  next h =>
    specialize ih ( n - ( s.length + 1 ) ) ( by omega ) ( "o" ++ s )
    convert ih rfl using 1
    rw [ String.length_append, show "o".length = 1 by rfl]
    grind


theorem padWithO_length (n : Nat) (s : String) : (padWithO n s).length = max n s.length := by
  exact h_pad_length n s


example (n : Nat) (s : String) (h : n ≥ s.length): (padWithO n s).length = n := by
  rw [ padWithO_length, max_eq_left h ]
