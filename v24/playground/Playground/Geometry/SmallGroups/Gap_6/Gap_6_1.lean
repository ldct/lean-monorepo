import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z6 := Multiplicative (ZMod 6)

#eval Fintype.card Z6
#eval Group.IsAbelian Z6
#eval Group.FracInvolutions Z6
#eval Group.CommutingFraction Z6
#eval Group.numSubgroups Z6
