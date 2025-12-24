import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih14 := DihedralGroup 14

#eval Fintype.card Dih14
#eval Group.IsAbelian Dih14
#eval Group.FracInvolutions Dih14
#eval Group.CommutingFraction Dih14
