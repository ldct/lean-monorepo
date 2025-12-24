import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev E9 := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

#eval Fintype.card E9
#eval Group.IsAbelian E9
#eval Group.FracInvolutions E9
#eval Group.CommutingFraction E9
