# Experimental editor header snapshot

This is a bounded prototype for reusing Lean's eager `--incr-header-save` image in a file worker. It is tied to `Playground/Scratch.lean`, the isolated stage2 build, and the generated compatibility manifest under `.lake/infoview-investigation/parser-environment`.

## Result

The implementation is correct under the tested editor operations, but it is not a performance improvement over the active optimized toolchain. Four alternating warm runs, all with the existing setup cache hit and no filesystem setup scan, measured:

| runtime | median fresh open | median worker RSS |
| --- | ---: | ---: |
| active optimized runtime | 3.429 s | 1678.9 MB |
| isolated rebuilt runtime, ordinary import | 4.983 s | 1974.1 MB |
| isolated rebuilt runtime, validated snapshot hit | 5.029 s | 1740.0 MB |

Every snapshot run contained explicit `LEAN_SERVER_SNAPSHOT hit` telemetry. The snapshot configuration was 1.600 s slower and used 61.1 MB more RSS than the active runtime, so it was not selected for the normal VS Code configuration.

The per-worker validator checks device, inode, size, mtime, and ctime for the exact 52,490 mapped files listed by the snapshot `.deps` sidecar. It also checks the snapshot, sidecar, setup JSON, executable and all linked Lean runtime libraries, project configuration, effective loader paths, and the direct Mathlib trace. A warm validation costs about 0.54 s. Validation runs in the worker launcher on every worker spawn; unsupported files and mismatches use the ordinary import path. This is separate from the removed broad setup-cache project scan.

## Reproduce

The patch is in `lean-server-snapshot.patch`. Apply it to an isolated copy of the optimized Lean source and rebuild stage2. Do not apply it to the active source tree. Save the snapshot eagerly (`LEAN_LAZY_PARTS=0`) using the editor setup JSON and server options `-DElab.inServer=true -DElab.async=true -Dinternal.cmdlineSnapshots=false`. Loading uses the normal lazy runtime.

The generated experiment currently lives at:

- isolated prefix: `.lake/infoview-investigation/parser-environment/lean4-server-snapshot/build/release/stage2`
- snapshot: `.lake/infoview-investigation/parser-environment/server-scratch.snap`
- manifest: `.lake/infoview-investigation/parser-environment/server-scratch.manifest.json`

From the playground root, an opt-in direct server is:

```sh
scripts/experimental-server-snapshot/server-snapshot-launcher.py --server "$PWD"
```

The launcher sets itself as `LEAN_WORKER_PATH`, validates each exact Scratch worker, preserves the installed no-scan setup-file cache through `LAKE`, and runs other workers without a snapshot. The checked-in launcher is reversible because it does not replace the active toolchain. Stop the server and use the ordinary `lake serve` command to roll back.

Correctness was checked with `scripts/check-editor-snapshot.py`: plain goals, `Lean.Widget.getInteractiveGoals`, an intentional proof error and correction, missing unsaved import and restoration, and a source-position-shifted header all passed. The missing import and shifted header reported explicit fallback rather than a false hit.

For a temporary VS Code check, the local linked toolchain `lean-v4.33.1-server-snapshot` points at the wrapper root. Save `lean-toolchain`, replace its one line with that name, run **Lean 4: Restart Server**, and open `Playground/Scratch.lean`. Restore the saved `lean-toolchain` and restart the server to roll back. The manifest permits exactly these two toolchain-file values: `lean-v4.33.1-optimized` and `lean-v4.33.1-server-snapshot`.

The rebuilt runtime had a lazy-parts index hit but no matching tactic image for its extension-set key, while the active runtime had a 93-extension tactic image. This is a known comparison confounder. It does not change the decision because the end-to-end candidate is slower than the active configuration; no cause is assigned to the rebuilt binary layout.
