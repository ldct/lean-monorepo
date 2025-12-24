import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih15 := DihedralGroup 15

#eval Fintype.card Dih15
#eval Group.IsAbelian Dih15
#eval Group.FracInvolutions Dih15
#eval Group.CommutingFraction Dih15
#eval Group.numSubgroups Dih15
