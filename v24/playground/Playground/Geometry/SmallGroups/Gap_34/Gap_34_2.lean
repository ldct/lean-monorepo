import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z34 := Multiplicative (ZMod 34)

#eval Fintype.card Z34
#eval Group.IsAbelian Z34
#eval Group.FracInvolutions Z34
#eval Group.CommutingFraction Z34
#eval Group.numSubgroups Z34
