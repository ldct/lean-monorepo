import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z33 := Multiplicative (ZMod 33)

#eval Fintype.card Z33
#eval Group.IsAbelian Z33
#eval Group.FracInvolutions Z33
#eval Group.CommutingFraction Z33
#eval Group.numSubgroups Z33
