import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih22 := DihedralGroup 22

#eval Fintype.card Dih22
#eval Group.IsAbelian Dih22
#eval Group.FracInvolutions Dih22
#eval Group.CommutingFraction Dih22
