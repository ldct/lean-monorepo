import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev A4 := AlternatingGroup (Fin 4)

#eval Fintype.card A4
#eval Group.IsAbelian A4
#eval Group.FracInvolutions A4
#eval Group.CommutingFraction A4
