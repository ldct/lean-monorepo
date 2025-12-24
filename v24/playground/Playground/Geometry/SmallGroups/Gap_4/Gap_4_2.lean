import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev V4 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

#eval Fintype.card V4
#eval Group.IsAbelian V4
#eval Group.FracInvolutions V4
#eval Group.CommutingFraction V4
#eval Group.numSubgroups V4
