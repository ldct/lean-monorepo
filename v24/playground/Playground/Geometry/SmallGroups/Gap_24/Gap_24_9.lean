import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C12 := Multiplicative (ZMod 2) × Multiplicative (ZMod 12)

#eval Fintype.card C2_C12
#eval Group.IsAbelian C2_C12
#eval Group.FracInvolutions C2_C12
#eval Group.CommutingFraction C2_C12
