import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z54 := Multiplicative (ZMod 54)

#eval Fintype.card Z54
#eval Group.IsAbelian Z54
#eval Group.FracInvolutions Z54
#eval Group.CommutingFraction Z54
