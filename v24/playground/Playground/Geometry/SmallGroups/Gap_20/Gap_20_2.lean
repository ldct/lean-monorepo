import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z20 := Multiplicative (ZMod 20)

#eval Fintype.card Z20
#eval Group.IsAbelian Z20
#eval Group.FracInvolutions Z20
#eval Group.CommutingFraction Z20
