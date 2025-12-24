import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Gap_8_2 := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)

#eval Fintype.card Gap_8_2
#eval Group.IsAbelian Gap_8_2
#eval Group.FracInvolutions Gap_8_2
#eval Group.CommutingFraction Gap_8_2
