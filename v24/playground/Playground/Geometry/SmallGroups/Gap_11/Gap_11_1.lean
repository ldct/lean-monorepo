import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z11 := Multiplicative (ZMod 11)

#eval Fintype.card Z11
#eval Group.IsAbelian Z11
#eval Group.FracInvolutions Z11
#eval Group.CommutingFraction Z11
#eval Group.numSubgroups Z11
