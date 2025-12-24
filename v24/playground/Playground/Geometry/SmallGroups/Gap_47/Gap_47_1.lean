import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z47 := Multiplicative (ZMod 47)

#eval Fintype.card Z47
#eval Group.IsAbelian Z47
#eval Group.FracInvolutions Z47
#eval Group.CommutingFraction Z47
#eval Group.numSubgroups Z47
