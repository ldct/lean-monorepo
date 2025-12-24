import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z16 := Multiplicative (ZMod 16)

#eval Fintype.card Z16
#eval Group.IsAbelian Z16
#eval Group.FracInvolutions Z16
#eval Group.CommutingFraction Z16
#eval Group.numSubgroups Z16
