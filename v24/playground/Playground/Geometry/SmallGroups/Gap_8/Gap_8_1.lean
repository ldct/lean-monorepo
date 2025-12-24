import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z8 := Multiplicative (ZMod 8)

#eval Fintype.card Z8
#eval Group.IsAbelian Z8
#eval Group.FracInvolutions Z8
#eval Group.CommutingFraction Z8
#eval Group.numSubgroups Z8
