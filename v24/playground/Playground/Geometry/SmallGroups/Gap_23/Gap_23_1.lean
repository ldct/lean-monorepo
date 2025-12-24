import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z23 := Multiplicative (ZMod 23)

#eval Fintype.card Z23
#eval Group.IsAbelian Z23
#eval Group.FracInvolutions Z23
#eval Group.CommutingFraction Z23
