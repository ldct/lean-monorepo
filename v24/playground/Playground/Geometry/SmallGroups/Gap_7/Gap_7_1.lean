import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z7 := Multiplicative (ZMod 7)

#eval Fintype.card Z7
#eval Group.IsAbelian Z7
#eval Group.FracInvolutions Z7
#eval Group.CommutingFraction Z7
