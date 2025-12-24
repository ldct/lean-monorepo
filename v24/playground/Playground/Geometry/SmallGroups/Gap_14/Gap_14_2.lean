import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z14 := Multiplicative (ZMod 14)

#eval Fintype.card Z14
#eval Group.IsAbelian Z14
#eval Group.FracInvolutions Z14
#eval Group.CommutingFraction Z14
