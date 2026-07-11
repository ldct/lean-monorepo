/-
Regenerates per-class tooltip metadata for site/normedfield_hierarchy.html:
  * per-class: docstring, pretty-printed type, isAbbrev flag
  * per-class: direct parents (projection name, subobject vs synthesized, doc, type)
  * per-class: own constructor fields (excluding subobject embeddings), with
    projection name, doc, and pretty-printed projection type
  * per-class: addedOverParents (own fields not provided by any direct parent's
    flattened field set) and copiedFromParents (own fields Lean copied into the
    constructor because overlapping parents cannot be subobjects)
  * per-class: fieldCount = size of the flattened field set (own fields plus
    everything inherited, subobject embeddings excluded)
Diagram aliases NPow/ZPow/NSMul/ZSMul duplicate the entry of the real Lean
class (Pow/SMul) and add `leanName` + `note`; the real classes also get their
own entries since they occur as `parents` targets.
Input:  scripts/hierarchy_input.json  (nodes; alias handling is hardcoded below)
Output: site/tooltip_data.json  (formatted like Python json.dumps(..., ensure_ascii=False))
Run:    lake env lean scripts/extract_tooltip_data.lean
-/
import Mathlib

open Lean Meta Elab

structure InputSpec where
  nodes : Array String
  deriving FromJson

/-- Diagram aliases: label, real Lean class, note text (order matters: it fixes
the tail order of the output array). -/
def aliasSpecs : Array (String × Name × String) := #[
  ("NPow",  `Pow,  "Diagram label for the ℕ-power operation; implemented by Lean class Pow with exponent type ℕ in these hierarchy nodes."),
  ("ZPow",  `Pow,  "Diagram label for the ℤ-power operation; implemented by Lean class Pow with exponent type ℤ in these hierarchy nodes."),
  ("NSMul", `SMul, "Diagram label for the ℕ-scalar multiplication operation; implemented by Lean class SMul with scalar type ℕ in these hierarchy nodes."),
  ("ZSMul", `SMul, "Diagram label for the ℤ-scalar multiplication operation; implemented by Lean class SMul with scalar type ℤ in these hierarchy nodes.")]

/-- Real Lean classes backing the aliases, in first-appearance order; they get
their own entries (they are referenced by name from `parents` arrays). -/
def aliasTargets : Array Name := #[`Pow, `SMul]

/-! ## JSON with insertion-ordered objects, rendered Python-style -/

/-- Minimal JSON value with insertion-ordered object keys. -/
inductive JV where
  | str (s : String)
  | bool (b : Bool)
  | nat (n : Nat)
  | arr (xs : Array JV)
  | obj (kvs : Array (String × JV))

/-- Escape a string the way Python's `json.dumps(..., ensure_ascii=False)` does. -/
def escapePy (s : String) : String := Id.run do
  let mut out : String := ""
  for c in s.toList do
    out := out ++
      (if c == '"' then "\\\""
       else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n"
       else if c == '\t' then "\\t"
       else if c == '\r' then "\\r"
       else if c.toNat == 8 then "\\b"
       else if c.toNat == 12 then "\\f"
       else if c.toNat < 32 then
         let ds := Nat.toDigits 16 c.toNat
         "\\u" ++ String.ofList (List.replicate (4 - ds.length) '0' ++ ds)
       else String.singleton c)
  return out

/-- Render like `json.dumps(..., ensure_ascii=False)` (", " and ": " separators). -/
partial def JV.render : JV → String
  | .str s => "\"" ++ escapePy s ++ "\""
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .arr xs => "[" ++ ", ".intercalate (xs.toList.map JV.render) ++ "]"
  | .obj kvs => "{" ++ ", ".intercalate (kvs.toList.map fun (k, v) =>
      "\"" ++ escapePy k ++ "\": " ++ v.render) ++ "}"

/-! ## Structure inspection -/

/-- Literal constructor fields of `n` that are not subobject embeddings, in
declaration order. -/
def ownFieldInfos (env : Environment) (n : Name) : Array StructureFieldInfo :=
  match getStructureInfo? env n with
  | some si => si.fieldNames.filterMap fun f =>
      match getFieldInfo? env n f with
      | some fi => if fi.subobject?.isNone then some fi else none
      | none => none
  | none => #[]

/-- Flattened field-name set of `n`: own (non-subobject) fields plus, recursively,
those of all direct parents. Memoized in `cache`. -/
partial def flatFields (env : Environment) (cache : IO.Ref (Std.HashMap Name (Std.HashSet Name)))
    (n : Name) : IO (Std.HashSet Name) := do
  if let some s := (← cache.get).get? n then return s
  let mut s : Std.HashSet Name := {}
  for fi in ownFieldInfos env n do
    s := s.insert fi.fieldName
  for p in getStructureParentInfo env n do
    for x in (← flatFields env cache p.structName) do
      s := s.insert x
  cache.modify (·.insert n s)
  return s

set_option maxHeartbeats 0 in
#eval show Elab.Command.CommandElabM Unit from do
  let inputRaw ← IO.FS.readFile "scripts/hierarchy_input.json"
  let spec : InputSpec ← IO.ofExcept do
    (Json.parse inputRaw).bind fromJson?
  Elab.Command.liftTermElabM do
    let env ← getEnv
    let cache ← IO.mkRef ({} : Std.HashMap Name (Std.HashSet Name))

    -- The reference data was rendered at width 100 (Lean's default is 120).
    let ppTypeOf (n : Name) : Elab.TermElabM String := do
      return (← Meta.ppExpr (← getConstInfo n).type).pretty 100
    let docOf (n : Name) : Elab.TermElabM String := do
      return (← findDocString? env n).getD ""

    -- Entry body (all keys except leading `name`) for a real Lean class.
    let buildBase (real : Name) : Elab.TermElabM (Array (String × JV)) := do
      let ci ← getConstInfo real
      let tyStr ← ppTypeOf real
      let doc ← docOf real
      if !isStructure env real then
        -- abbrev / plain definition (e.g. IsNoetherianRing)
        let note ← match ci.value? with
          | some v => Meta.lambdaTelescope v fun xs body => do
              let mut args := ""
              for x in xs do
                let d ← x.fvarId!.getDecl
                if d.binderInfo == .default then
                  args := args ++ " " ++ toString d.userName
              pure s!"Abbrev, not a structure/class with fields: {real}{args} := {(← Meta.ppExpr body).pretty 100}."
          | none => pure s!"Abbrev, not a structure/class with fields: {real}."
        return #[("doc", .str doc), ("type", .str tyStr), ("isAbbrev", .bool true),
                 ("parents", .arr #[]), ("ownFields", .arr #[]),
                 ("addedOverParents", .arr #[]), ("fieldCount", .nat 0),
                 ("note", .str note)]
      -- structure class
      let mut parentsJV : Array JV := #[]
      let mut parentFlat : Std.HashSet Name := {}
      for p in getStructureParentInfo env real do
        parentsJV := parentsJV.push (.obj #[
          ("doc", .str (← docOf p.structName)),
          ("name", .str (toString p.structName)),
          ("projection", .str (toString p.projFn)),
          ("subobject", .bool p.subobject),
          ("type", .str (← ppTypeOf p.structName))])
        for x in (← flatFields env cache p.structName) do
          parentFlat := parentFlat.insert x
      let mut ownJV : Array JV := #[]
      let mut addedJV : Array JV := #[]
      let mut copied : Array String := #[]
      for fi in ownFieldInfos env real do
        let fjv : JV := .obj #[
          ("doc", .str (← docOf fi.projFn)),
          ("kind", .str "field"),
          ("name", .str (toString fi.fieldName)),
          ("owner", .str (toString real)),
          ("proj", .str (toString fi.projFn)),
          ("type", .str (← ppTypeOf fi.projFn))]
        ownJV := ownJV.push fjv
        if parentFlat.contains fi.fieldName then
          copied := copied.push (toString fi.fieldName)
        else
          addedJV := addedJV.push fjv
      let flatN := (← flatFields env cache real).size
      -- invariant check: our union matches Lean's flattened field list
      let leanFlatN := (getStructureFieldsFlattened env real false
        |>.foldl (fun (s : Std.HashSet Name) x => s.insert x) {}).size
      if flatN != leanFlatN then
        IO.println s!"WARNING {real}: field union {flatN} != getStructureFieldsFlattened {leanFlatN}"
      let mut b : Array (String × JV) := #[
        ("doc", .str doc), ("type", .str tyStr), ("isAbbrev", .bool false),
        ("parents", .arr parentsJV), ("ownFields", .arr ownJV),
        ("addedOverParents", .arr addedJV), ("fieldCount", .nat flatN)]
      if copied.size > 0 then
        b := b.push ("copiedFromParents", .arr (copied.map JV.str))
      return b

    -- Output order: diagram nodes minus aliases, then alias targets, then aliases.
    let mut jobs : Array (String × Name) := #[]
    for n in spec.nodes do
      unless aliasSpecs.any (·.1 == n) do
        jobs := jobs.push (n, n.toName)
    for t in aliasTargets do
      jobs := jobs.push (toString t, t)
    for (a, real, _) in aliasSpecs do
      jobs := jobs.push (a, real)

    let mut baseCache : Std.HashMap Name (Array (String × JV)) := {}
    let mut entries : Array JV := #[]
    for (disp, real) in jobs do
      let base ← match baseCache.get? real with
        | some b => pure b
        | none => do
            let b ← buildBase real
            baseCache := baseCache.insert real b
            pure b
      let mut pairs := #[("name", JV.str disp)] ++ base
      if let some (_, _, note) := aliasSpecs.find? (·.1 == disp) then
        pairs := pairs.push ("leanName", .str (toString real))
        pairs := pairs.push ("note", .str note)
      entries := entries.push (.obj pairs)

    let out := "[" ++ ", ".intercalate (entries.toList.map JV.render) ++ "]"
    IO.FS.writeFile "site/tooltip_data.json" out
    IO.println s!"wrote site/tooltip_data.json ({entries.size} entries)"
