import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion



set_option linter.style.longLine false

abbrev Gap_60_11 := Equiv.Perm (Fin 3) × Multiplicative (ZMod 10)
