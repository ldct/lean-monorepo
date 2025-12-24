import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C4_C4 := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

#eval Fintype.card C4_C4
#eval Group.IsAbelian C4_C4
#eval Group.FracInvolutions C4_C4
#eval Group.CommutingFraction C4_C4
#eval Group.numSubgroups C4_C4
