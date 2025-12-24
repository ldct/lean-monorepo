import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z30 := Multiplicative (ZMod 30)

#eval Fintype.card Z30
#eval Group.IsAbelian Z30
#eval Group.FracInvolutions Z30
#eval Group.CommutingFraction Z30
#eval Group.numSubgroups Z30
