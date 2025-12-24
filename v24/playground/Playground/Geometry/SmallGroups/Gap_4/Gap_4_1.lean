import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z4 := Multiplicative (ZMod 4)

#eval Fintype.card Z4
#eval Group.IsAbelian Z4
#eval Group.FracInvolutions Z4
#eval Group.CommutingFraction Z4
#eval Group.numSubgroups Z4
