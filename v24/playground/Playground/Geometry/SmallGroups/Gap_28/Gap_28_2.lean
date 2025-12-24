import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z28 := Multiplicative (ZMod 28)

#eval Fintype.card Z28
#eval Group.IsAbelian Z28
#eval Group.FracInvolutions Z28
#eval Group.CommutingFraction Z28
