import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z43 := Multiplicative (ZMod 43)

#eval Fintype.card Z43
#eval Group.IsAbelian Z43
#eval Group.FracInvolutions Z43
#eval Group.CommutingFraction Z43
