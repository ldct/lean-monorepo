import Playground.Lagarias.Bounds
import Lean.Util.CollectAxioms

/-!
Audit every declaration in the helper namespace, not just a selected theorem.
The final RH equivalence is deliberately not included: it is still incomplete.
Run this file explicitly after building `Playground.Lagarias.Bounds`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `LeanEval.NumberTheory.Lagarias
  let declarations := env.constants.toList.filter fun entry => root.isPrefixOf entry.1
  if declarations.isEmpty then
    throwError "Lagarias audit found no declarations; check the imports and namespace"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
    unless forbidden.isEmpty do
      throwError "{name} depends on forbidden axioms: {forbidden}"
  logInfo m!"Audited {declarations.length} Lagarias helper declarations: only propext, Classical.choice, and Quot.sound are permitted."
