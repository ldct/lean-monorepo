import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z31 := Multiplicative (ZMod 31)

#eval Fintype.card Z31
#eval Group.IsAbelian Z31
#eval Group.FracInvolutions Z31
#eval Group.CommutingFraction Z31
