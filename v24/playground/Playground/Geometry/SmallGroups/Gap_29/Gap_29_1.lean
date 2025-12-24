import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z29 := Multiplicative (ZMod 29)

#eval Fintype.card Z29
#eval Group.IsAbelian Z29
#eval Group.FracInvolutions Z29
#eval Group.CommutingFraction Z29
