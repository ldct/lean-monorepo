import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C3_C12 := Multiplicative (ZMod 3) × Multiplicative (ZMod 12)

#eval Fintype.card C3_C12
#eval Group.IsAbelian C3_C12
#eval Group.FracInvolutions C3_C12
#eval Group.CommutingFraction C3_C12
#eval Group.numSubgroups C3_C12
