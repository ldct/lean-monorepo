
- IsUpperTriangular
- simproc for `det_of_lowerTriangular`
- PR `#register_hint 1 decide +revert` to register `decide +revert` as a hint
- Quaternion.lean, line 96 - simp lemma for ZMod 2n
- simproc for computing order in a finite group by verifying factors
- n \ne 0 in ZMod 2n
- Quaternion.lean, line 229 - rfl
- https://en.wikipedia.org/wiki/Hurwitz_quaternion - use grind like in GaussianInt
- simproc for cancelling 

example (a b c d e : ℕ) (h : a + b + c = a + d + e) : False := by
  simp at h
  grind