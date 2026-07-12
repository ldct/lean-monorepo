/-
Extracts extra hierarchy metadata for site/normedfield_hierarchy.html:
  * per-field: isProp (data vs law), default value, tactic-autoParam status  (proposals 1, 2)
  * per-class: isProp (mixin vs data class), instance matrix over a roster    (proposals 2, 3)
  * per-edge: backing declaration name, priority, docstring                   (proposal 4)
  * per-class: constructor-style declarations (induced / Injective / of*)     (proposal 6)
Input:  scripts/hierarchy_input.json  (nodes, edges, owners, roster)
Output: site/hierarchy_extras.json
Note:   since Mathlib PR #38036 (v4.32.0-rc1-patch1) NPow/ZPow/NSMul/ZSMul are
        ordinary classes, so diagram names map 1:1 to Lean names (no aliases).
Run:    lake env lean scripts/extract_hierarchy_extras.lean
-/
import Mathlib

open Lean Meta Elab

structure RosterTy where
  term : String
  disp : String
  deriving FromJson

structure EdgeIn where
  s : String
  t : String
  kind : String
  deriving FromJson

structure InputSpec where
  nodes : Array String
  edges : Array EdgeIn
  owners : Array String
  roster : Array RosterTy
  deriving FromJson

/-- Term string `C (T)` for the instance-matrix synthesis check. -/
def appliedTerm (diagName ty : String) : String :=
  s!"{diagName} ({ty})"

/-- Does `e` (an application, possibly with loose bvars) match the diagram class? -/
def matchesClass (real : Name) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n == real
  | _ => false

/-- Syntactically collect the ∀-binders (info, type) and the body. -/
partial def collectBinders : Expr → Array (BinderInfo × Expr) → Array (BinderInfo × Expr) × Expr
  | .forallE _ t b bi, acc => collectBinders b (acc.push (bi, t))
  | e, acc => (acc, e)

def truncStr (s : String) (n : Nat) : String :=
  let s := s.replace "\n" " "
  if s.length > n then String.ofList (s.toList.take n) ++ " …" else s

def ppOneLine (e : Expr) (maxLen : Nat := 180) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  return truncStr (" ".intercalate (s.splitOn "\n" |>.map (fun l => l.trimAsciiStart.toString))) maxLen

/-- Pretty default value of field `S.f`, if any. -/
def defaultValueStr (env : Environment) (S f : Name) : MetaM (Option String) := do
  let some fn := getDefaultFnForField? env S f | return none
  let some ci := env.find? fn | return none
  let some v := ci.value? | return none
  Meta.lambdaTelescope v fun _ body => do
    let mut b := body
    while b.isAppOfArity ``id 2 do
      b := b.appArg!
    return some (← ppOneLine b 90)

def jStrOpt : Option String → Json
  | some s => Json.str s
  | none => Json.null

set_option maxHeartbeats 0 in
#eval show Elab.Command.CommandElabM Unit from do
  let inputRaw ← IO.FS.readFile "scripts/hierarchy_input.json"
  let spec : InputSpec ← IO.ofExcept do
    (Json.parse inputRaw).bind fromJson?
  Elab.Command.liftTermElabM do
    let env ← getEnv

    -- ================= per-class isProp =================
    let classIsProp : Std.HashMap String Bool := Id.run do
      let mut m := {}
      for n in spec.nodes do
        let real := n.toName
        let isP := match env.find? real with
          | some ci =>
            let (_, body) := collectBinders ci.type #[]
            body == .sort .zero
          | none => false
        m := m.insert n isP
      return m

    -- ================= per-field info (proposals 1 & 2) =================
    -- keyed "Owner.field" (matches `proj` in tooltip data)
    let mut fieldJson : Array (String × Json) := #[]
    for ownerStr in spec.owners do
      let owner := ownerStr.toName
      let some sinfo := getStructureInfo? env owner | continue
      let ctor := (getStructureCtor env owner).name
      let some ctorCi := env.find? ctor | continue
      let fieldSet := sinfo.fieldNames.foldl (fun (s : NameSet) n => s.insert n) {}
      let (binders, _) := collectBinders ctorCi.type #[]
      -- binder user names are lost syntactically; use Meta telescope for names
      let entries ← Meta.forallTelescope ctorCi.type fun xs _ => do
        let mut out : Array (String × Json) := #[]
        for x in xs, (bi, _) in binders do
          let nm ← x.fvarId!.getUserName
          unless fieldSet.contains nm do continue
          let _ := bi
          let t ← Meta.inferType x
          let isAuto := t.isAppOfArity ``autoParam 2
          let core := if isAuto then t.getAppArgs[0]! else t
          let isP ← try Meta.isProp core catch _ => pure false
          let dflt ← try defaultValueStr env owner nm catch _ => pure none
          out := out.push (s!"{owner}.{nm}", Json.mkObj
            [("isProp", Json.bool isP),
             ("autoParam", Json.bool isAuto),
             ("default", jStrOpt dflt)])
        return out
      fieldJson := fieldJson ++ entries
    IO.println s!"fields extracted: {fieldJson.size}"

    -- ================= instance matrix (proposal 3) =================
    let mut matrix : Std.HashMap String (Array Nat) := {}
    let mut rosterHits : Array Nat := Array.replicate spec.roster.size 0
    for cls in spec.nodes do
      let mut hits : Array Nat := #[]
      for h : i in [0:spec.roster.size] do
        let ty := spec.roster[i].term
        let ok ← withCurrHeartbeats <| withOptions (fun o => o.set `maxHeartbeats (200000 : Nat)) do
          try
            match Parser.runParserCategory env `term (appliedTerm cls ty) with
            | .error _ => pure false
            | .ok stx =>
              Elab.Term.withoutErrToSorry do
                let e ← Elab.Term.elabTerm stx none
                Elab.Term.synthesizeSyntheticMVarsNoPostponing
                let e ← instantiateMVars e
                if e.hasSorry || e.hasExprMVar then pure false
                else pure (← Meta.synthInstance? e).isSome
          catch _ => pure false
        if ok then
          hits := hits.push i
          rosterHits := rosterHits.set! i (rosterHits[i]! + 1)
      matrix := matrix.insert cls hits
    for h : i in [0:spec.roster.size] do
      IO.println s!"roster {spec.roster[i].disp}: {rosterHits[i]!} classes"

    -- ================= edge declarations (proposal 4) =================
    -- pre-scan the instance table once
    let instState := Meta.instanceExtension.getState env
    let mut instInfos : Array (Name × Nat × Expr) := #[]  -- name, priority, type
    for (n, entry) in instState.instanceNames.toList do
      if let some ci := env.find? n then
        instInfos := instInfos.push (n, entry.priority, ci.type)
    IO.println s!"instances scanned: {instInfos.size}"

    -- edges whose derivation is genuinely multi-hop in Mathlib; label the key instance
    let manualEdgeDecl : List (String × Name) :=
      [("MetricSpace->T2Space", `instT2SpaceOfR1SpaceOfT0Space),
       ("PseudoEMetricSpace->FirstCountableTopology", `UniformSpace.firstCountableTopology)]
    let mut edgeJson : Array (String × Json) := #[]
    let mut unresolved : Array String := #[]
    for e in spec.edges do
      let realS := e.s.toName
      let realT := e.t.toName
      -- 1. direct projection S.toT
      let projName : Name := Name.str e.s.toName ("to" ++ e.t)
      let mut decl : Option Name := none
      if let some (_, d) := manualEdgeDecl.find? (·.1 == s!"{e.s}->{e.t}") then
        decl := some d
      else if env.contains projName then
        decl := some projName
      else
        -- 2. instance-table search: result matches T, some inst-binder matches S
        let mut best : Option (Name × Nat) := none  -- name, score
        for (n, _, ty) in instInfos do
          let (binders, body) := collectBinders ty #[]
          unless matchesClass realT body do continue
          let instBinders := binders.filter (fun (bi, _) => bi == .instImplicit)
          unless instBinders.any (fun (_, t) => matchesClass realS t) do continue
          let score := instBinders.size * 1000 + (toString n).length
          match best with
          | some (_, s) => if score < s then best := some (n, score)
          | none => best := some (n, score)
        decl := best.map (·.1)
      match decl with
      | none =>
        unresolved := unresolved.push s!"{e.s}->{e.t}"
        edgeJson := edgeJson.push (s!"{e.s}->{e.t}", Json.mkObj
          [("kind", Json.str e.kind), ("decl", Json.null)])
      | some d =>
        let prio := instState.instanceNames.find? d |>.map (·.priority)
        let doc ← findDocString? env d
        let tyStr ← match env.find? d with
          | some ci => some <$> ppOneLine ci.type 220
          | none => pure none
        edgeJson := edgeJson.push (s!"{e.s}->{e.t}", Json.mkObj
          [("kind", Json.str e.kind),
           ("decl", Json.str (toString d)),
           ("prio", match prio with | some p => toJson p | none => Json.null),
           ("doc", jStrOpt doc),
           ("type", jStrOpt tyStr)])
    IO.println s!"edges resolved: {edgeJson.size - unresolved.size}/{edgeJson.size}; unresolved: {unresolved}"

    -- ================= constructors (proposal 6) =================
    let realToDiag : Std.HashMap Name String := Id.run do
      let mut m := {}
      for n in spec.nodes do
        m := m.insert n.toName n
      return m
    let interesting (n : Name) : Option Nat :=  -- rank
      match n with
      | .str p last =>
        if last == "induced" then some 0
        else if (`Function.Injective).isPrefixOf n || ((toString p).splitOn ".").contains "Injective" then some 1
        else if last.length > 2 && last.startsWith "of" && ((last.toList.drop 2).headD 'a').isUpper then some 2
        else if (`Equiv).isPrefixOf n && n.components.length == 2 then some 3
        else if last == "mk'" then some 4
        else none
      | _ => none
    let mut ctorCandidates : Array (String × Nat × Name) := #[]  -- diagClass, rank, decl
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      let some rank := interesting n | continue
      match ci with
      | .defnInfo _ | .thmInfo _ =>
        let (_, body) := collectBinders ci.type #[]
        let fn := body.getAppFn
        match fn with
        | .const c _ =>
          if let some diag := realToDiag.get? c then
            if !(instState.instanceNames.contains n) then
              ctorCandidates := ctorCandidates.push (diag, rank, n)
        | _ => pure ()
      | _ => pure ()
    IO.println s!"ctor candidates: {ctorCandidates.size}"
    let mut ctorsByClass : Std.HashMap String (Array (Nat × Name)) := {}
    for (diag, rank, n) in ctorCandidates do
      ctorsByClass := ctorsByClass.insert diag ((ctorsByClass.getD diag #[]).push (rank, n))

    -- ================= assemble =================
    let mut classJson : Array (String × Json) := #[]
    for cls in spec.nodes do
      let ctors := (ctorsByClass.getD cls #[]).qsort
        (fun a b => a.1 < b.1 || (a.1 == b.1 && toString a.2 < toString b.2))
      let totalCtors := ctors.size
      let mut ctorArr : Array Json := #[]
      for (_, n) in ctors.toSubarray 0 (min 10 ctors.size) do
        let doc ← findDocString? env n
        let tyStr ← match env.find? n with
          | some ci => some <$> ppOneLine ci.type 220
          | none => pure none
        ctorArr := ctorArr.push (Json.mkObj
          [("name", Json.str (toString n)),
           ("doc", jStrOpt (doc.map (truncStr · 220))),
           ("type", jStrOpt tyStr)])
      classJson := classJson.push (cls, Json.mkObj
        [("isProp", Json.bool (classIsProp.getD cls false)),
         ("insts", Json.arr ((matrix.getD cls #[]).map (fun i => toJson i))),
         ("ctors", Json.arr ctorArr),
         ("ctorTotal", toJson totalCtors)])

    let out := Json.mkObj
      [("roster", Json.arr (spec.roster.map (fun r => Json.mkObj
          [("term", Json.str r.term), ("disp", Json.str r.disp)]))),
       ("classes", Json.mkObj classJson.toList),
       ("fields", Json.mkObj fieldJson.toList),
       ("edges", Json.mkObj edgeJson.toList)]
    IO.FS.writeFile "site/hierarchy_extras.json" out.compress
    IO.println "wrote site/hierarchy_extras.json"
