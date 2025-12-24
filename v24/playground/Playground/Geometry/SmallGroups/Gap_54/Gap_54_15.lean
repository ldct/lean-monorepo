import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C3_C3_C6 := Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 6)

#eval Fintype.card C3_C3_C6
#eval Group.IsAbelian C3_C3_C6
#eval Group.FracInvolutions C3_C3_C6
#eval Group.CommutingFraction C3_C3_C6
