import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z52 := Multiplicative (ZMod 52)

#eval Fintype.card Z52
#eval Group.IsAbelian Z52
#eval Group.FracInvolutions Z52
#eval Group.CommutingFraction Z52
#eval Group.numSubgroups Z52
