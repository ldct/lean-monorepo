import Mathlib.Tactic

example : n + n = 2*n := by
  plausible

example (hn : n > 5): n + n = 2*n := by
  plausible
