import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C6_C6 := Multiplicative (ZMod 6) × Multiplicative (ZMod 6)

#eval Fintype.card C6_C6
#eval Group.IsAbelian C6_C6
#eval Group.FracInvolutions C6_C6
#eval Group.CommutingFraction C6_C6
