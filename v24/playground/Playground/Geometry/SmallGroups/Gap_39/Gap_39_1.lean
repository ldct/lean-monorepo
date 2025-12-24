import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z39 := Multiplicative (ZMod 39)

#eval Fintype.card Z39
#eval Group.IsAbelian Z39
#eval Group.FracInvolutions Z39
#eval Group.CommutingFraction Z39
#eval Group.numSubgroups Z39
