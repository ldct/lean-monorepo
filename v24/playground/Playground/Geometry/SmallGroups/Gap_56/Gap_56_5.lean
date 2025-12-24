import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih28 := DihedralGroup 28

#eval Fintype.card Dih28
#eval Group.IsAbelian Dih28
#eval Group.FracInvolutions Dih28
#eval Group.CommutingFraction Dih28
