import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih12 := DihedralGroup 12

#eval Fintype.card Dih12
#eval Group.IsAbelian Dih12
#eval Group.FracInvolutions Dih12
#eval Group.CommutingFraction Dih12
#eval Group.numSubgroups Dih12
