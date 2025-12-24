import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih18 := DihedralGroup 18

#eval Fintype.card Dih18
#eval Group.IsAbelian Dih18
#eval Group.FracInvolutions Dih18
#eval Group.CommutingFraction Dih18
#eval Group.numSubgroups Dih18
