import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z25 := Multiplicative (ZMod 25)

#eval Fintype.card Z25
#eval Group.IsAbelian Z25
#eval Group.FracInvolutions Z25
#eval Group.CommutingFraction Z25
