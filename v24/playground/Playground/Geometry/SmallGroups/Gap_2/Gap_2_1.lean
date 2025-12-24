import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z2 := Multiplicative (ZMod 2)

#eval Fintype.card Z2
#eval Group.IsAbelian Z2
#eval Group.FracInvolutions Z2
#eval Group.CommutingFraction Z2
