import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z48 := Multiplicative (ZMod 48)

#eval Fintype.card Z48
#eval Group.IsAbelian Z48
#eval Group.FracInvolutions Z48
#eval Group.CommutingFraction Z48
