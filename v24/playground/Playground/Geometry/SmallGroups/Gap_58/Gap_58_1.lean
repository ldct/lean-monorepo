import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih29 := DihedralGroup 29

#eval Fintype.card Dih29
#eval Group.IsAbelian Dih29
#eval Group.FracInvolutions Dih29
#eval Group.CommutingFraction Dih29
