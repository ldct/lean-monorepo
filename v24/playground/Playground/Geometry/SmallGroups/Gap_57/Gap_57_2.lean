import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z57 := Multiplicative (ZMod 57)

#eval Fintype.card Z57
#eval Group.IsAbelian Z57
#eval Group.FracInvolutions Z57
#eval Group.CommutingFraction Z57
#eval Group.numSubgroups Z57
