import Playground.Geometry.Chapter_2_1

-- Exercise 2.1.1.c

namespace Ex_2_1_1_cd
open Chapter_2_1

example (n : PNat): AddSubgroup ℚ := AddSubgroup.ofAddSubgroupCriterion
{ a | a.den ∣ n }
(by
  use 0
  simp
)
(by
  rintro x hx y hy
  simp at *
  sorry
)

-- Exercise 2.1.1.d
example (n : PNat) : AddSubgroup ℚ := AddSubgroup.ofAddSubgroupCriterion
{ a | Nat.gcd a.den n = 1 }
(by
  use 0
  simp
)
(by
  rintro x hx y hy
  simp at *
  sorry
)


end Ex_2_1_1_cd