import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z10 := Multiplicative (ZMod 10)

#eval Fintype.card Z10
#eval Group.IsAbelian Z10
#eval Group.FracInvolutions Z10
#eval Group.CommutingFraction Z10
