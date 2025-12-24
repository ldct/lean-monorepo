import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Q := QuaternionGroup 2

deriving instance Repr for QuaternionGroup

#eval Fintype.card Q
#eval Group.IsAbelian Q
#eval Group.FracInvolutions Q
