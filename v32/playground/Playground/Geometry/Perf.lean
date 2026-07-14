import Playground.Geometry.Dicyclic
import Playground.Geometry.SmallGroups.GroupProps
import Mathlib.GroupTheory.SpecificGroups.Dihedral



namespace Perf
open DicyclicGroup

set_option maxRecDepth 10000

deriving instance Repr for DihedralGroup


#reduce Z1 (DihedralGroup 16)

#reduce Z2 (DihedralGroup 16)

#reduce Z3 (DihedralGroup 16)

#reduce Z4 (DihedralGroup 16)


end Perf