import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z17 := Multiplicative (ZMod 17)

#eval Fintype.card Z17
#eval Group.IsAbelian Z17
#eval Group.FracInvolutions Z17
#eval Group.CommutingFraction Z17
#eval Group.numSubgroups Z17
