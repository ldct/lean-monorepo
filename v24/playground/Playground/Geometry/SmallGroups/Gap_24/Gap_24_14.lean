import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev C2_C2_S3 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)
