import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C28 := Multiplicative (ZMod 2) × Multiplicative (ZMod 28)

#eval Fintype.card C2_C28
#eval Group.IsAbelian C2_C28
#eval Group.FracInvolutions C2_C28
#eval Group.CommutingFraction C2_C28
