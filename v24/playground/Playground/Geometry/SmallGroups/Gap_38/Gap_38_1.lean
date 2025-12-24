import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih19 := DihedralGroup 19

#eval Fintype.card Dih19
#eval Group.IsAbelian Dih19
#eval Group.FracInvolutions Dih19
#eval Group.CommutingFraction Dih19
