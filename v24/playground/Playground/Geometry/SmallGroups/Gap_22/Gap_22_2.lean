import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z22 := Multiplicative (ZMod 22)

#eval Fintype.card Z22
#eval Group.IsAbelian Z22
#eval Group.FracInvolutions Z22
#eval Group.CommutingFraction Z22
#eval Group.numSubgroups Z22
