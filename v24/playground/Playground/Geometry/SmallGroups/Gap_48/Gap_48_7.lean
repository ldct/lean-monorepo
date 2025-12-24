import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih24 := DihedralGroup 24

#eval Fintype.card Dih24
#eval Group.IsAbelian Dih24
#eval Group.FracInvolutions Dih24
#eval Group.CommutingFraction Dih24
#eval Group.numSubgroups Dih24
