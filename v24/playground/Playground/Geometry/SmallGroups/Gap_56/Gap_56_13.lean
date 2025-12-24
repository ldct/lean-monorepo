import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C2_C14 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 14)

#eval Fintype.card C2_C2_C14
#eval Group.IsAbelian C2_C2_C14
#eval Group.FracInvolutions C2_C2_C14
#eval Group.CommutingFraction C2_C2_C14
