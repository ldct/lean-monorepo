import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih21 := DihedralGroup 21

#eval Fintype.card Dih21
#eval Group.IsAbelian Dih21
#eval Group.FracInvolutions Dih21
#eval Group.CommutingFraction Dih21
#eval Group.numSubgroups Dih21
