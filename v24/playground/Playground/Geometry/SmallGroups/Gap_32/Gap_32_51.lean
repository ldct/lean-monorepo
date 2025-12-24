import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C2_C2_C2_C2 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

#eval Fintype.card C2_C2_C2_C2_C2
#eval Group.IsAbelian C2_C2_C2_C2_C2
#eval Group.FracInvolutions C2_C2_C2_C2_C2
#eval Group.CommutingFraction C2_C2_C2_C2_C2
#eval Group.numSubgroups C2_C2_C2_C2_C2
