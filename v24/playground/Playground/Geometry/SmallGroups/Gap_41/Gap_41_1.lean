import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z41 := Multiplicative (ZMod 41)

#eval Fintype.card Z41
#eval Group.IsAbelian Z41
#eval Group.FracInvolutions Z41
#eval Group.CommutingFraction Z41
