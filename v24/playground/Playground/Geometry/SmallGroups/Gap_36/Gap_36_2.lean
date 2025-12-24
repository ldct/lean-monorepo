import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z36 := Multiplicative (ZMod 36)

#eval Fintype.card Z36
#eval Group.IsAbelian Z36
#eval Group.FracInvolutions Z36
#eval Group.CommutingFraction Z36
