import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z59 := Multiplicative (ZMod 59)

#eval Fintype.card Z59
#eval Group.IsAbelian Z59
#eval Group.FracInvolutions Z59
#eval Group.CommutingFraction Z59
#eval Group.numSubgroups Z59
