import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C5_C10 := Multiplicative (ZMod 5) × Multiplicative (ZMod 10)

#eval Fintype.card C5_C10
#eval Group.IsAbelian C5_C10
#eval Group.FracInvolutions C5_C10
#eval Group.CommutingFraction C5_C10
#eval Group.numSubgroups C5_C10
