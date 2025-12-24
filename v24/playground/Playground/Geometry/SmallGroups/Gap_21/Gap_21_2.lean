import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z21 := Multiplicative (ZMod 21)

#eval Fintype.card Z21
#eval Group.IsAbelian Z21
#eval Group.FracInvolutions Z21
#eval Group.CommutingFraction Z21
#eval Group.numSubgroups Z21
