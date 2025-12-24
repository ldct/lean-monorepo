import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih27 := DihedralGroup 27

#eval Fintype.card Dih27
#eval Group.IsAbelian Dih27
#eval Group.FracInvolutions Dih27
#eval Group.CommutingFraction Dih27
#eval Group.numSubgroups Dih27
