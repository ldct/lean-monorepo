import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z9 := Multiplicative (ZMod 9)

#eval Fintype.card Z9
#eval Group.IsAbelian Z9
#eval Group.FracInvolutions Z9
#eval Group.CommutingFraction Z9
