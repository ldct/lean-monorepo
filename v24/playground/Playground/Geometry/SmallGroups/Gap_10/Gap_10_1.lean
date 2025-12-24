import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih5 := DihedralGroup 5

#eval Fintype.card Dih5
#eval Group.IsAbelian Dih5
#eval Group.FracInvolutions Dih5
#eval Group.CommutingFraction Dih5
