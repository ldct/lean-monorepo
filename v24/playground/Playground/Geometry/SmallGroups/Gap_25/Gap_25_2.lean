import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C5_C5 := Multiplicative (ZMod 5) × Multiplicative (ZMod 5)

#eval Fintype.card C5_C5
#eval Group.IsAbelian C5_C5
#eval Group.FracInvolutions C5_C5
#eval Group.CommutingFraction C5_C5
