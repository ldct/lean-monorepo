import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih23 := DihedralGroup 23

#eval Fintype.card Dih23
#eval Group.IsAbelian Dih23
#eval Group.FracInvolutions Dih23
#eval Group.CommutingFraction Dih23
