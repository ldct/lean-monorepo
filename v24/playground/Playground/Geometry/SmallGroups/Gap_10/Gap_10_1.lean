import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev D10 := DihedralGroup 5

#eval Fintype.card D10
#eval Group.IsAbelian D10
#eval Group.FracInvolutions D10
#eval Group.CommutingFraction D10
