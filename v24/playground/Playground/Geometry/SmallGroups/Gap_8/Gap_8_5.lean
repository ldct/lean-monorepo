import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev E8 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

#eval Fintype.card E8
#eval Group.IsAbelian E8
#eval Group.FracInvolutions E8
#eval Group.CommutingFraction E8
#eval Group.numSubgroups E8
