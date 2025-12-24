import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z27 := Multiplicative (ZMod 27)

#eval Fintype.card Z27
#eval Group.IsAbelian Z27
#eval Group.FracInvolutions Z27
#eval Group.CommutingFraction Z27
