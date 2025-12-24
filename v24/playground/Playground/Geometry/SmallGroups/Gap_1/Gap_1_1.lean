import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Trivial := Multiplicative (ZMod 1)

#eval Fintype.card Trivial
#eval Group.IsAbelian Trivial
#eval Group.FracInvolutions Trivial
#eval Group.CommutingFraction Trivial
#eval Group.numSubgroups Trivial
