import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev S4 := Equiv.Perm (Fin 4)

#eval Fintype.card S4
#eval Group.IsAbelian S4
#eval Group.FracInvolutions S4
#eval Group.CommutingFraction S4
#eval Group.numSubgroups S4
