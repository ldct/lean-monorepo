import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih11 := DihedralGroup 11

#eval Fintype.card Dih11
#eval Group.IsAbelian Dih11
#eval Group.FracInvolutions Dih11
#eval Group.CommutingFraction Dih11
