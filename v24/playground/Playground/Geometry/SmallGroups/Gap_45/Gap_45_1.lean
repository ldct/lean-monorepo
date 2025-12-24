import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z45 := Multiplicative (ZMod 45)

#eval Fintype.card Z45
#eval Group.IsAbelian Z45
#eval Group.FracInvolutions Z45
#eval Group.CommutingFraction Z45
#eval Group.numSubgroups Z45
