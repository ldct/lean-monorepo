import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z32 := Multiplicative (ZMod 32)

#eval Fintype.card Z32
#eval Group.IsAbelian Z32
#eval Group.FracInvolutions Z32
#eval Group.CommutingFraction Z32
