import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z49 := Multiplicative (ZMod 49)

#eval Fintype.card Z49
#eval Group.IsAbelian Z49
#eval Group.FracInvolutions Z49
#eval Group.CommutingFraction Z49
