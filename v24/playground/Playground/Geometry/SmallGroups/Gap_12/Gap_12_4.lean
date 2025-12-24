import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih6 := DihedralGroup 6

#eval Fintype.card Dih6
#eval Group.IsAbelian Dih6
#eval Group.FracInvolutions Dih6
#eval Group.CommutingFraction Dih6
#eval Group.numSubgroups Dih6
