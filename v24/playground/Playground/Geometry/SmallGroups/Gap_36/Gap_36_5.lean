import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C18 := Multiplicative (ZMod 2) × Multiplicative (ZMod 18)

#eval Fintype.card C2_C18
#eval Group.IsAbelian C2_C18
#eval Group.FracInvolutions C2_C18
#eval Group.CommutingFraction C2_C18
#eval Group.numSubgroups C2_C18
