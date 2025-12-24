import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C4_C12 := Multiplicative (ZMod 4) × Multiplicative (ZMod 12)

#eval Fintype.card C4_C12
#eval Group.IsAbelian C4_C12
#eval Group.FracInvolutions C4_C12
#eval Group.CommutingFraction C4_C12
