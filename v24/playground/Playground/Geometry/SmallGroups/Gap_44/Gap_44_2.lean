import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z44 := Multiplicative (ZMod 44)

#eval Fintype.card Z44
#eval Group.IsAbelian Z44
#eval Group.FracInvolutions Z44
#eval Group.CommutingFraction Z44
#eval Group.numSubgroups Z44
