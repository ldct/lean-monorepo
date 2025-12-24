import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih7 := DihedralGroup 7

#eval Fintype.card Dih7
#eval Group.IsAbelian Dih7
#eval Group.FracInvolutions Dih7
#eval Group.CommutingFraction Dih7
#eval Group.numSubgroups Dih7
