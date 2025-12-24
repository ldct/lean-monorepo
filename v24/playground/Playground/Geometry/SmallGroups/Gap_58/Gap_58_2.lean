import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z58 := Multiplicative (ZMod 58)

#eval Fintype.card Z58
#eval Group.IsAbelian Z58
#eval Group.FracInvolutions Z58
#eval Group.CommutingFraction Z58
