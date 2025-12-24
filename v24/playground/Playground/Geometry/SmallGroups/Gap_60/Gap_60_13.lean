import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C30 := Multiplicative (ZMod 2) × Multiplicative (ZMod 30)

#eval Fintype.card C2_C30
#eval Group.IsAbelian C2_C30
#eval Group.FracInvolutions C2_C30
#eval Group.CommutingFraction C2_C30
#eval Group.numSubgroups C2_C30
