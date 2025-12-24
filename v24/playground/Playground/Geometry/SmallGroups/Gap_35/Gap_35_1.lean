import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z35 := Multiplicative (ZMod 35)

#eval Fintype.card Z35
#eval Group.IsAbelian Z35
#eval Group.FracInvolutions Z35
#eval Group.CommutingFraction Z35
