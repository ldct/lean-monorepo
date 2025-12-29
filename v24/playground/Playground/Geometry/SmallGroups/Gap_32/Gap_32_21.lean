import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion



set_option linter.style.longLine false

abbrev Gap_32_21 := Multiplicative (ZMod 2) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
