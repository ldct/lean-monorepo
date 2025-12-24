import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih20 := DihedralGroup 20

#eval Fintype.card Dih20
#eval Group.IsAbelian Dih20
#eval Group.FracInvolutions Dih20
#eval Group.CommutingFraction Dih20
#eval Group.numSubgroups Dih20
