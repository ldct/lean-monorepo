/-
Discovery pass for the staging-only expanded NormedField hierarchy.

Discovers every eligible unary structure class in the pinned Mathlib v4.32.0
environment, records its direct `extends` parents, and records every direct
unary implication

    ∀ (α : Type u) [Source α], Target α

among that universe.  “Eligible” means a non-deprecated structure class with
exactly one explicit non-Prop type argument, all remaining class parameters
instance-implicit.  Consumers close the current staging seed set under these
two relations and exclude every fully-qualified name containing `Lean.Grind`.

Output: scripts/hierarchy_discovery_staging.json
Run:    lake env lean scripts/discover_hierarchy_staging.lean
-/
import Mathlib

open Lean Meta Elab

partial def collectBinders : Expr → Array (BinderInfo × Expr) → Array (BinderInfo × Expr) × Expr
  | .forallE _ t b bi, acc => collectBinders b (acc.push (bi, t))
  | e, acc => (acc, e)

def stripOutParam (e : Expr) : Expr :=
  if e.isAppOfArity ``outParam 1 || e.isAppOfArity ``semiOutParam 1 then e.appArg! else e

/-- Recognize `C α ...`, where `α` is the indicated loose bound variable. -/
def classAppOf (e : Expr) (k : Nat) : Option Name :=
  match e.getAppFn with
  | .const cn _ =>
    let args := e.getAppArgs
    if args.size ≥ 1 && args[0]! == .bvar k then some cn else none
  | _ => none

set_option maxHeartbeats 0 in
#eval show Elab.Command.CommandElabM Unit from do
  Elab.Command.liftTermElabM do
    let env ← getEnv
    let modOf (n : Name) : Option Name := do
      let idx ← env.getModuleIdxFor? n
      env.header.moduleNames[(idx : Nat)]?

    let mut candidates : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      unless isClass env n && isStructure env n do continue
      if Lean.Linter.isDeprecated env n then continue
      let (binders, body) := collectBinders ci.type #[]
      if binders.size == 0 then continue
      let (bi0, t0) := binders[0]!
      unless bi0 == .default do continue
      let t0Ok := match stripOutParam t0 with
        | .sort l => !l.isZero
        | _ => false
      unless t0Ok do continue
      unless (binders.extract 1 binders.size).all (fun (bi, _) => bi == .instImplicit) do continue
      unless body.isSort do continue
      if (toString n).contains "Decidable" then continue
      candidates := candidates.push n
    let cands := candidates.qsort (fun a b => a.toString < b.toString)
    let classSet : NameSet := cands.foldl (fun s n => s.insert n) {}
    IO.println s!"eligible unary structure classes: {cands.size}"

    let mut classesJ : Array Json := #[]
    for c in cands do
      let parents := (getStructureParentInfo env c).map (·.structName)
      classesJ := classesJ.push (Json.mkObj [
        ("name", Json.str (toString c)),
        ("module", Json.str (toString ((modOf c).getD Name.anonymous))),
        ("parents", Json.arr (parents.map (fun p => Json.str (toString p))))])

    let instState := Meta.instanceExtension.getState env
    let mut edgeMap : Std.HashMap (Name × Name) Name := {}
    for (n, _) in instState.instanceNames.toList do
      let some ci := env.find? n | continue
      let (binders, body) := collectBinders ci.type #[]
      unless binders.size == 2 do continue
      let (_, t0) := binders[0]!
      let (bi1, t1) := binders[1]!
      unless bi1 == .instImplicit do continue
      let t0Ok := match stripOutParam t0 with
        | .sort l => !l.isZero
        | _ => false
      unless t0Ok do continue
      let some source := classAppOf t1 0 | continue
      let some target := classAppOf body 1 | continue
      unless classSet.contains source && classSet.contains target && source != target do continue
      let key := (source, target)
      match edgeMap.get? key with
      | none => edgeMap := edgeMap.insert key n
      | some old =>
        -- Stable canonical declaration: shortest fully-qualified name, then lexical.
        let ns := toString n
        let os := toString old
        if ns.length < os.length || (ns.length == os.length && ns < os) then
          edgeMap := edgeMap.insert key n

    let mut edges : Array (Name × Name × Name) := #[]
    for ((s, t), n) in edgeMap.toList do edges := edges.push (s, t, n)
    edges := edges.qsort fun a b =>
      let ak := s!"{a.1}\u0000{a.2.1}\u0000{a.2.2}"
      let bk := s!"{b.1}\u0000{b.2.1}\u0000{b.2.2}"
      decide (ak < bk)
    IO.println s!"eligible unary instance pairs: {edges.size}"
    let edgeJ := edges.map fun (s, t, n) => Json.mkObj [
      ("source", Json.str (toString s)),
      ("target", Json.str (toString t)),
      ("decl", Json.str (toString n))]
    let out := Json.mkObj [
      ("mathlibRev", Json.str "81a5d257c8e410db227a6665ed08f64fea08e997"),
      ("classes", Json.arr classesJ),
      ("unaryInstances", Json.arr edgeJ)]
    IO.FS.writeFile "scripts/hierarchy_discovery_staging.json" out.pretty
    IO.println "wrote scripts/hierarchy_discovery_staging.json"
