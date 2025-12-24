import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z26 := Multiplicative (ZMod 26)

#eval Fintype.card Z26
#eval Group.IsAbelian Z26
#eval Group.FracInvolutions Z26
#eval Group.CommutingFraction Z26
#eval Group.numSubgroups Z26
