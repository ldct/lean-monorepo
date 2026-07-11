/-
Per-class tooltip metadata for site/real_instances.html (classes satisfied by ℝ).
Adapted from scripts/extract_tooltip_data.lean; differences:
  * input scripts/real_input.json (nodes are fully-qualified Lean names, e.g.
    `Order.Frame`; no diagram aliases — every node is a real class)
  * output site/real_tooltip_data.json
Same output schema: per-class docstring, pretty type, isAbbrev flag, direct
parents, own constructor fields, addedOverParents / copiedFromParents,
flattened fieldCount.
Run: lake env lean scripts/extract_real_tooltip_data.lean
-/
import Mathlib

open Lean Meta Elab

structure InputSpec where
  nodes : Array String
  deriving FromJson

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
  let inputRaw ← IO.FS.readFile "scripts/real_input.json"
  let spec : InputSpec ← IO.ofExcept do
    (Json.parse inputRaw).bind fromJson?
  Elab.Command.liftTermElabM do
    let env ← getEnv
    let cache ← IO.mkRef ({} : Std.HashMap Name (Std.HashSet Name))

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
        -- abbrev / plain definition; the discovery pass excludes these, but keep
        -- the branch so the script degrades gracefully
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

    let mut entries : Array JV := #[]
    for n in spec.nodes do
      let base ← buildBase n.toName
      entries := entries.push (.obj (#[("name", JV.str n)] ++ base))

    let out := "[" ++ ", ".intercalate (entries.toList.map JV.render) ++ "]"
    IO.FS.writeFile "site/real_tooltip_data.json" out
    IO.println s!"wrote site/real_tooltip_data.json ({entries.size} entries)"
