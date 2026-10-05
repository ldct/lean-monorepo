import Lake.CLI.Main
import Lake.CLI.Serve
import Lake.Load.Workspace
import Lake.Build.Run
import Lake.Build.Module

open Lean Lake

def mark (label : String) (start : Nat) : IO Nat := do
  let now ← IO.monoNanosNow
  IO.eprintln s!"{label}: {(now - start) / 1000000} ms"
  return now

def main : IO Unit := do
  let start ← IO.monoNanosNow
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let opts : LakeOptions := { elanInstall?, leanInstall?, lakeInstall?, noCache := some true }
  let cfg ← opts.mkLoadConfig |>.toIO (fun e => IO.userError (toString e))
  let t ← mark "configuration" start
  let bc : BuildConfig := { noBuild := true }
  let some ws ← loadWorkspace cfg |>.toBaseIO bc.toLogConfig
    | throw <| IO.userError "workspace failed"
  let t ← mark "workspace" t
  let path ← IO.FS.realPath "Playground/Scratch.lean"
  let result ← (ws.runBuild (cfg := bc) do setupServerModule path.toString path none).toBaseIO
  let .ok setup := result | throw <| IO.userError "setup failed"
  let t ← mark "dependency setup" t
  let str := (toJson setup).compress
  IO.FS.writeFile ".lake/infoview-investigation/instrumented.json" str
  let t ← mark "serialize + write" t
  let parsed ← IO.ofExcept (Json.parse str >>= (fromJson? (α := ModuleSetup)))
  let _ ← mark s!"parse ({parsed.importArts.size} imports)" t
  pure ()
