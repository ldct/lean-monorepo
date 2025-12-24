import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih9 := DihedralGroup 9

#eval Fintype.card Dih9
#eval Group.IsAbelian Dih9
#eval Group.FracInvolutions Dih9
#eval Group.CommutingFraction Dih9
