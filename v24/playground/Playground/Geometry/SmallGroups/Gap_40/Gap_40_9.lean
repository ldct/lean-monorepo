import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C20 := Multiplicative (ZMod 2) × Multiplicative (ZMod 20)

#eval Fintype.card C2_C20
#eval Group.IsAbelian C2_C20
#eval Group.FracInvolutions C2_C20
#eval Group.CommutingFraction C2_C20
