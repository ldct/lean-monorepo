import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z40 := Multiplicative (ZMod 40)

#eval Fintype.card Z40
#eval Group.IsAbelian Z40
#eval Group.FracInvolutions Z40
#eval Group.CommutingFraction Z40
#eval Group.numSubgroups Z40
