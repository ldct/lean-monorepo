import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z24 := Multiplicative (ZMod 24)

#eval Fintype.card Z24
#eval Group.IsAbelian Z24
#eval Group.FracInvolutions Z24
#eval Group.CommutingFraction Z24
