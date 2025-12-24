import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev D8 := DihedralGroup 4

#eval Fintype.card D8
#eval Group.IsAbelian D8 = true
#eval Group.FracInvolutions D8
