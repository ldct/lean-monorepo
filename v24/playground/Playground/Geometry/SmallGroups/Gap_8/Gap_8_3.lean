import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih4 := DihedralGroup 4

#eval Fintype.card Dih4
#eval Group.IsAbelian Dih4
#eval Group.FracInvolutions Dih4
#eval Group.CommutingFraction Dih4
