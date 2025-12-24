import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C16 := Multiplicative (ZMod 2) × Multiplicative (ZMod 16)

#eval Fintype.card C2_C16
#eval Group.IsAbelian C2_C16
#eval Group.FracInvolutions C2_C16
#eval Group.CommutingFraction C2_C16
