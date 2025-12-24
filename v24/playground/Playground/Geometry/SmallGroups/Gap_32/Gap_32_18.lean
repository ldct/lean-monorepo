import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih16 := DihedralGroup 16

#eval Fintype.card Dih16
#eval Group.IsAbelian Dih16
#eval Group.FracInvolutions Dih16
#eval Group.CommutingFraction Dih16
#eval Group.numSubgroups Dih16
