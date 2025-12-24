import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih30 := DihedralGroup 30

#eval Fintype.card Dih30
#eval Group.IsAbelian Dih30
#eval Group.FracInvolutions Dih30
#eval Group.CommutingFraction Dih30
