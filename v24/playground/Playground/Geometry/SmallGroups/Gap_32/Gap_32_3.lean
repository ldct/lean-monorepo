import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C4_C8 := Multiplicative (ZMod 4) × Multiplicative (ZMod 8)

#eval Fintype.card C4_C8
#eval Group.IsAbelian C4_C8
#eval Group.FracInvolutions C4_C8
#eval Group.CommutingFraction C4_C8
#eval Group.numSubgroups C4_C8
