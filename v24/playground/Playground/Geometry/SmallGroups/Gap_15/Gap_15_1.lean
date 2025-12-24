import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z15 := Multiplicative (ZMod 15)

#eval Fintype.card Z15
#eval Group.IsAbelian Z15
#eval Group.FracInvolutions Z15
#eval Group.CommutingFraction Z15
#eval Group.numSubgroups Z15
