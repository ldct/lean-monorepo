import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih13 := DihedralGroup 13

#eval Fintype.card Dih13
#eval Group.IsAbelian Dih13
#eval Group.FracInvolutions Dih13
#eval Group.CommutingFraction Dih13
#eval Group.numSubgroups Dih13
