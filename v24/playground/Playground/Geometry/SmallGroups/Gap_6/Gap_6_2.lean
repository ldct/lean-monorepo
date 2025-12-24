import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev S3 := Equiv.Perm (Fin 3)

#eval Fintype.card S3
#eval Group.IsAbelian S3
#eval Group.FracInvolutions S3
#eval Group.CommutingFraction S3
