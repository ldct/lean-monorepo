import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z46 := Multiplicative (ZMod 46)

#eval Fintype.card Z46
#eval Group.IsAbelian Z46
#eval Group.FracInvolutions Z46
#eval Group.CommutingFraction Z46
