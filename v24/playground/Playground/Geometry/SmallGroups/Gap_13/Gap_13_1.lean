import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z13 := Multiplicative (ZMod 13)

#eval Fintype.card Z13
#eval Group.IsAbelian Z13
#eval Group.FracInvolutions Z13
#eval Group.CommutingFraction Z13
#eval Group.numSubgroups Z13
