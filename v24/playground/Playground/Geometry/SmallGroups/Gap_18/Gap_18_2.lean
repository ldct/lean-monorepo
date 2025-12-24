import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z18 := Multiplicative (ZMod 18)

#eval Fintype.card Z18
#eval Group.IsAbelian Z18
#eval Group.FracInvolutions Z18
#eval Group.CommutingFraction Z18
