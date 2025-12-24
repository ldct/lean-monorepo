import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih25 := DihedralGroup 25

#eval Fintype.card Dih25
#eval Group.IsAbelian Dih25
#eval Group.FracInvolutions Dih25
#eval Group.CommutingFraction Dih25
#eval Group.numSubgroups Dih25
