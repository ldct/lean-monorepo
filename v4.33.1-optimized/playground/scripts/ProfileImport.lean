import Lean
open Lean

def stamp (label : String) (start : Nat) : IO Nat := do
  let now ← IO.monoNanosNow
  IO.eprintln s!"PHASE {label} {now - start}"
  return now

def main (args : List String) : IO Unit := do
  let start ← IO.monoNanosNow
  initSearchPath (← findSysroot)
  let rows ← IO.mkRef (#[] : Array (Name × Nat))
  if args.contains "extensions" then
    let descrs ← persistentEnvExtensionsRef.get
    persistentEnvExtensionsRef.set (descrs.map fun d => { d with addImportedFn := fun entries ctx => do
      let t ← IO.monoNanosNow
      let s ← d.addImportedFn entries ctx
      let endTime ← IO.monoNanosNow
      rows.modify (·.push (d.name, endTime - t))
      return s })
  let arts ← if let some file ← IO.getEnv "PROFILE_IMPORT_SETUP" then do
    let setup ← IO.ofExcept (Json.parse (← IO.FS.readFile file) >>= (fromJson? (α := ModuleSetup)))
    pure setup.importArts
  else pure {}
  let t ← stamp "probe_setup" start
  withImporting do
    unsafe enableInitializersExecution
    let imports : Array Import := #[{module := `Mathlib}]
    let (_, state) ← (importModulesCore imports (arts := arts)).run
    let t ← stamp "importModulesCore" t
    let env ← finalizeImport state imports {} 0 true (!(args.contains "noext"))
    let _ ← stamp "finalizeImport" t
    IO.eprintln s!"MODULES {env.header.moduleNames.size}"
  for (name, ns) in ← rows.get do
    IO.eprintln s!"EXT {name} {ns}"
