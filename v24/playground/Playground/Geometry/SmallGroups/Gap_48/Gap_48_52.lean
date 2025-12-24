import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C2_C2_C6 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)

#eval Fintype.card C2_C2_C2_C6
#eval Group.IsAbelian C2_C2_C2_C6
#eval Group.FracInvolutions C2_C2_C2_C6
#eval Group.CommutingFraction C2_C2_C2_C6
