import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C2_C10 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 10)

#eval Fintype.card C2_C2_C10
#eval Group.IsAbelian C2_C2_C10
#eval Group.FracInvolutions C2_C2_C10
#eval Group.CommutingFraction C2_C2_C10
#eval Group.numSubgroups C2_C2_C10
