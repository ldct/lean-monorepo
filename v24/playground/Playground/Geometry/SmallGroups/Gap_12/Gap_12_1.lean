import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dic12 := DicyclicGroup 3

#eval Fintype.card Dic12
#eval Group.IsAbelian Dic12
#eval Group.FracInvolutions Dic12
#eval Group.CommutingFraction Dic12
