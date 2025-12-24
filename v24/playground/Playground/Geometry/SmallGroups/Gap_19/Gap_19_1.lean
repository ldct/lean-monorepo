import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z19 := Multiplicative (ZMod 19)

#eval Fintype.card Z19
#eval Group.IsAbelian Z19
#eval Group.FracInvolutions Z19
#eval Group.CommutingFraction Z19
#eval Group.numSubgroups Z19
