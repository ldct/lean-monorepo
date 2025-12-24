import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z12 := Multiplicative (ZMod 12)

#eval Fintype.card Z12
#eval Group.IsAbelian Z12
#eval Group.FracInvolutions Z12
#eval Group.CommutingFraction Z12
#eval Group.numSubgroups Z12
