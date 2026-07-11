/-
Discovery pass for site/real_instances.html: every class `C` in the environment
(with Mathlib imported) such that
  * `C` takes exactly one explicit argument, of shape `(α : Type u)` (a non-Prop
    sort), all remaining binders instance-implicit, and the result is a sort;
  * `C` is a structure (downstream tooltip/extras scripts assume structures);
  * `C` is not deprecated, not internal, and not `Decidable*` noise;
  * `synthInstance (C ℝ)` succeeds (elaborated via the term parser so trailing
    instance arguments, e.g. `[TopologicalSpace ℝ]` for `BorelSpace`, get
    synthesized; per-check heartbeat cap so nothing hangs the scan).

Also records, for downstream graph building (all done in Python afterwards):
  * per satisfied class: isProp (mixin), defining module, direct extends parents;
  * derived-instance implications: every instance of shape
      ∀ (α : Type u) [C₁ α] … [Cₖ α], D α     (k ≥ 1, single variable α)
    with D and all Cᵢ in the satisfied set, recorded as {d, hyps}.

Output: scripts/real_discovery.json
Run:    lake env lean scripts/discover_real_classes.lean   (slow: full Mathlib import + ~thousands of synthInstance checks)
-/
import Mathlib

open Lean Meta Elab

/-- Syntactically collect the ∀-binders (info, type) and the body. -/
partial def collectBinders : Expr → Array (BinderInfo × Expr) → Array (BinderInfo × Expr) × Expr
  | .forallE _ t b bi, acc => collectBinders b (acc.push (bi, t))
  | e, acc => (acc, e)

/-- Strip `outParam` / `semiOutParam` wrappers (e.g. `RCLike (K : semiOutParam (Type u))`). -/
def stripOutParam (e : Expr) : Expr :=
  if e.isAppOfArity ``outParam 1 || e.isAppOfArity ``semiOutParam 1 then e.appArg! else e

/-- Is `e` an application `C α ...` of a class to the type variable `α = bvar k`?
Trailing arguments (the class's own context instances, e.g. the `TopologicalSpace X`
argument in `@T1Space X inst`) are ignored. Returns the class name. -/
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

    -- ============ 1. candidates: single-Type-arg structure classes ============
    let mut nClasses := 0
    let mut nShape := 0
    let mut nNonStructure := 0
    let mut nDeprecated := 0
    let mut candidates : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      unless isClass env n do continue
      nClasses := nClasses + 1
      let (binders, body) := collectBinders ci.type #[]
      if binders.size == 0 then continue
      let (bi0, t0) := binders[0]!
      unless bi0 == .default do continue
      let t0Ok := match stripOutParam t0 with
        | .sort l => !l.isZero  -- `Type u` (or higher); excludes Prop-arg classes like Decidable
        | _ => false
      unless t0Ok do continue
      unless (binders.extract 1 binders.size).all (fun (bi, _) => bi == .instImplicit) do continue
      unless body.isSort do continue
      if ((toString n).splitOn "Decidable").length > 1 then continue  -- Decidable* noise
      nShape := nShape + 1
      unless isStructure env n do
        nNonStructure := nNonStructure + 1
        continue
      if Lean.Linter.isDeprecated env n then
        nDeprecated := nDeprecated + 1
        continue
      candidates := candidates.push n
    let cands := candidates.qsort (fun a b => a.toString < b.toString)
    IO.println s!"classes seen: {nClasses}; single-Type-arg shape: {nShape}; of those non-structures: {nNonStructure}, deprecated: {nDeprecated}; candidates: {cands.size}"

    -- ============ 2. synthInstance (C ℝ) for each candidate ============
    let mut satisfied : Array Name := #[]
    let mut parseFails : Array Name := #[]
    let mut idx := 0
    for c in cands do
      idx := idx + 1
      if idx % 200 == 0 then
        IO.println s!"progress {idx}/{cands.size}, satisfied so far: {satisfied.size}"
      -- result: none = parse failure, some b = synthesis outcome
      let res : Option Bool ← withCurrHeartbeats <| withOptions (fun o => o.set `maxHeartbeats (200000 : Nat)) do
        try
          match Parser.runParserCategory env `term s!"{c} ℝ" with
          | .error _ => pure none
          | .ok stx =>
            Elab.Term.withoutErrToSorry do
              let e ← Elab.Term.elabTerm stx none
              Elab.Term.synthesizeSyntheticMVarsNoPostponing
              let e ← instantiateMVars e
              if e.hasSorry || e.hasExprMVar then pure (some false)
              else pure (some (← Meta.synthInstance? e).isSome)
        catch _ => pure (some false)
      match res with
      | none => parseFails := parseFails.push c
      | some true => satisfied := satisfied.push c
      | some false => pure ()
    IO.println s!"satisfied by ℝ: {satisfied.size}/{cands.size} (parse failures: {parseFails.size} {parseFails.toList})"

    let satSet : NameSet := satisfied.foldl (fun s n => s.insert n) {}

    -- ============ 3. derived-instance implications among the satisfied set ============
    let instState := Meta.instanceExtension.getState env
    let mut instEdges : Array (Name × Name × Array Name) := #[]  -- (instName, D, hyps)
    for (n, _) in instState.instanceNames.toList do
      let some ci := env.find? n | continue
      let (binders, body) := collectBinders ci.type #[]
      let nB := binders.size
      if nB < 2 then continue
      let (_, t0) := binders[0]!
      let t0Ok := match t0 with
        | .sort l => !l.isZero
        | _ => false
      unless t0Ok do continue
      let d ← match classAppOf body (nB - 1) with
        | some dn => pure dn
        | none => continue
      unless satSet.contains d do continue
      let mut ok := true
      let mut hyps : Array Name := #[]
      for i in [1:nB] do
        let (bi, t) := binders[i]!
        let hyp := match bi, classAppOf t (i - 1) with
          | .instImplicit, some cn => if satSet.contains cn then some cn else none
          | _, _ => none
        match hyp with
        | some cn => hyps := hyps.push cn
        | none => ok := false
      if ok && hyps.size > 0 then
        instEdges := instEdges.push (n, d, hyps)
    IO.println s!"derived-instance implications (single type variable, all hyps satisfied): {instEdges.size}"

    -- ============ 4. reference counts (prominence): how many declarations
    -- mention each satisfied class in their TYPE ============
    let mut refCount : Std.HashMap Name Nat := {}
    for c in satisfied do
      refCount := refCount.insert c 0
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      let names := ci.type.foldConsts (∅ : NameSet) (fun cn s => s.insert cn)
      for cn in names do
        if let some k := refCount.get? cn then
          refCount := refCount.insert cn (k + 1)
    IO.println "reference counts computed"

    -- ============ 5. output ============
    let mut classesJ : Array Json := #[]
    for c in satisfied do
      let (binders, body) := collectBinders (← getConstInfo c).type #[]
      let parents := (getStructureParentInfo env c).map (·.structName)
      -- context classes: instance-implicit binders of the class's own type of
      -- shape `C α` where α is the class's type argument (binder 0)
      let mut ctx : Array Name := #[]
      for i in [1:binders.size] do
        let (_, t) := binders[i]!
        if let some cn := classAppOf t (i - 1) then ctx := ctx.push cn
      classesJ := classesJ.push (Json.mkObj [
        ("name", Json.str (toString c)),
        ("isProp", Json.bool (body == Expr.sort .zero)),
        ("module", Json.str (toString ((modOf c).getD Name.anonymous))),
        ("refCount", toJson (refCount.getD c 0)),
        ("context", Json.arr (ctx.map (fun p => Json.str (toString p)))),
        ("parents", Json.arr (parents.map (fun p => Json.str (toString p))))])
    let mut edgesJ : Array Json := #[]
    for (n, d, hyps) in instEdges do
      edgesJ := edgesJ.push (Json.mkObj [
        ("inst", Json.str (toString n)),
        ("d", Json.str (toString d)),
        ("hyps", Json.arr (hyps.map (fun h => Json.str (toString h))))])
    let out := Json.mkObj [
      ("counts", Json.mkObj [
        ("classesSeen", toJson (nClasses : Nat)),
        ("singleTypeArgShape", toJson (nShape : Nat)),
        ("nonStructureExcluded", toJson (nNonStructure : Nat)),
        ("deprecatedExcluded", toJson (nDeprecated : Nat)),
        ("candidates", toJson (cands.size : Nat)),
        ("satisfied", toJson (satisfied.size : Nat))]),
      ("satisfied", Json.arr classesJ),
      ("instEdges", Json.arr edgesJ)]
    IO.FS.writeFile "scripts/real_discovery.json" out.pretty
    IO.println "wrote scripts/real_discovery.json"
