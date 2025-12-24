import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z60 := Multiplicative (ZMod 60)

#eval Fintype.card Z60
#eval Group.IsAbelian Z60
#eval Group.FracInvolutions Z60
#eval Group.CommutingFraction Z60
