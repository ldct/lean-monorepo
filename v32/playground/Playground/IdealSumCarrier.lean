import Mathlib


namespace IdealSumCarrier

example {R} [Ring R] (I J : Ideal R)
: (I + J).carrier = {i + j | (i ∈ I.carrier) (j ∈ J.carrier) } := by sorry


end IdealSumCarrier