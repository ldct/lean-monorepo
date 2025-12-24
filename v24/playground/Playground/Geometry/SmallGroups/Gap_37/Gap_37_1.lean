import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z37 := Multiplicative (ZMod 37)

#eval Fintype.card Z37
#eval Group.IsAbelian Z37
#eval Group.FracInvolutions Z37
#eval Group.CommutingFraction Z37
