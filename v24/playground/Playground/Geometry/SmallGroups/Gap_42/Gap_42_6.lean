import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z42 := Multiplicative (ZMod 42)

#eval Fintype.card Z42
#eval Group.IsAbelian Z42
#eval Group.FracInvolutions Z42
#eval Group.CommutingFraction Z42
