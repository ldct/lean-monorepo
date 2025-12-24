import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev A5 := AlternatingGroup (Fin 5)

#eval Fintype.card A5
#eval Group.IsAbelian A5
#eval Group.FracInvolutions A5
#eval Group.CommutingFraction A5
