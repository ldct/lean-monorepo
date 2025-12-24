import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z38 := Multiplicative (ZMod 38)

#eval Fintype.card Z38
#eval Group.IsAbelian Z38
#eval Group.FracInvolutions Z38
#eval Group.CommutingFraction Z38
