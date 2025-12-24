import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z3 := Multiplicative (ZMod 3)

#eval Fintype.card Z3
#eval Group.IsAbelian Z3
#eval Group.FracInvolutions Z3
#eval Group.CommutingFraction Z3
#eval Group.numSubgroups Z3
