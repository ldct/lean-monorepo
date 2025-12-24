import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih26 := DihedralGroup 26

#eval Fintype.card Dih26
#eval Group.IsAbelian Dih26
#eval Group.FracInvolutions Dih26
#eval Group.CommutingFraction Dih26
