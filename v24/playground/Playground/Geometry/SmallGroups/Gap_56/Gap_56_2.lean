import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z56 := Multiplicative (ZMod 56)

#eval Fintype.card Z56
#eval Group.IsAbelian Z56
#eval Group.FracInvolutions Z56
#eval Group.CommutingFraction Z56
