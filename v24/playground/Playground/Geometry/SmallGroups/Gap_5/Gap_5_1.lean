import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z5 := Multiplicative (ZMod 5)

#eval Fintype.card Z5
#eval Group.IsAbelian Z5
#eval Group.FracInvolutions Z5
#eval Group.CommutingFraction Z5
