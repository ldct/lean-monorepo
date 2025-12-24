import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z51 := Multiplicative (ZMod 51)

#eval Fintype.card Z51
#eval Group.IsAbelian Z51
#eval Group.FracInvolutions Z51
#eval Group.CommutingFraction Z51
#eval Group.numSubgroups Z51
