import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z55 := Multiplicative (ZMod 55)

#eval Fintype.card Z55
#eval Group.IsAbelian Z55
#eval Group.FracInvolutions Z55
#eval Group.CommutingFraction Z55
#eval Group.numSubgroups Z55
