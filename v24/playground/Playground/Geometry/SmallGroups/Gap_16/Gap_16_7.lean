import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih8 := DihedralGroup 8

#eval Fintype.card Dih8
#eval Group.IsAbelian Dih8
#eval Group.FracInvolutions Dih8
#eval Group.CommutingFraction Dih8
