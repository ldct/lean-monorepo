import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z50 := Multiplicative (ZMod 50)

#eval Fintype.card Z50
#eval Group.IsAbelian Z50
#eval Group.FracInvolutions Z50
#eval Group.CommutingFraction Z50
