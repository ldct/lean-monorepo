import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih17 := DihedralGroup 17

#eval Fintype.card Dih17
#eval Group.IsAbelian Dih17
#eval Group.FracInvolutions Dih17
#eval Group.CommutingFraction Dih17
#eval Group.numSubgroups Dih17
