import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z53 := Multiplicative (ZMod 53)

#eval Fintype.card Z53
#eval Group.IsAbelian Z53
#eval Group.FracInvolutions Z53
#eval Group.CommutingFraction Z53
#eval Group.numSubgroups Z53
