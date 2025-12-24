import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih10 := DihedralGroup 10

#eval Fintype.card Dih10
#eval Group.IsAbelian Dih10
#eval Group.FracInvolutions Dih10
#eval Group.CommutingFraction Dih10
