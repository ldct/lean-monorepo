import Mathlib
import Playground.Geometry.SmallGroups.GroupProps
import Playground.Geometry.SmallGroups.AlternatingGroup

abbrev A4 := AlternatingGroup 4

#eval Fintype.card A4
#eval Group.IsAbelian A4
#eval Group.FracInvolutions A4
#eval Group.CommutingFraction A4
#eval Group.numSubgroups A4
