# Cursor / Lean Infoview startup investigation

Investigated on 2026-09-11 on an Apple M5 Max with 64 GiB RAM, macOS 26.5.2,
and Cursor's `leanprover.lean4` extension version 0.0.239.

## Finding and its limits

Opening `playground/Playground/Scratch.lean` showed an orange processing indicator
and an Infoview spinner with “No info found.” The user clarified that the delay
was on opening the file, rather than moving the cursor through checked proofs.

A direct language-server test reproduced approximately **13.47 seconds from
opening the file to completion**, followed by an **8 ms goal response**. A separate
`lake setup-file` invocation took **10.03 seconds**. This identifies per-file
project setup as a substantial part of the opening delay; it does not yet identify
the expensive operations inside that command.

The earlier bare-Lean benchmarks exclude this editor setup step. Their roughly
3-second import result must not be presented as expected editor opening latency.
See [the benchmark report](playground/BENCHMARKS.md).

Returning a large dependency map describes what setup does, but does **not**
establish that ten seconds is necessary. Filesystem overhead, dependency graph
processing, serialization, and other costs have not yet been separately profiled.

## Toolchain and cache verification

The live Cursor process tree contained:

```text
lean-v4.33.1-optimized/bin/lake serve
  .../stage2/bin/lean.real --server .../playground
    .../stage2/bin/lean.real --worker file:///.../Playground/Scratch.lean
```

`vmmap` of an actual Cursor file worker confirmed that it mapped:

- This project's `stage2/lib/lean/libleanshared.dylib`.
- `~/.cache/lean-lazy-parts/index-1781340539223832851.lazyparts`.
- `.lake/optimization-cache/tactics/exts-8883371632140020981.tacticindex`.

Thus the worker was using the optimized runtime **and** the generated tactic
image. Although an editor worker can have a different image key from a CLI process,
that general caveat did not prevent this particular worker from mapping the image.

The project uses Lean v4.33.1 with the performance patch and the separate codegen
fix, and the standard Mathlib v4.33.1 cache. **Do not rebuild Mathlib or compile its
native tactic libraries: the user explicitly excluded that work.** Pinned commits
and setup instructions are in [the playground README](playground/README.md).

`lean --version` cannot distinguish this fork from stock: it intentionally reports
the same version/hash for artifact compatibility. Check process paths and loaded
runtime libraries instead.

## What `lake setup-file` does

The file worker invokes Lake to determine how to check the opened document. Lake
loads the workspace, resolves the file's imports and their transitive dependencies,
checks required artifacts, and returns module settings and artifact locations as
JSON. The server can supply the unsaved editor header through standard input.

For this file the captured result contained:

- Module name `Playground.Scratch`, package `playground`.
- The project's Lean options, including `maxSynthPendingDepth = 3` and linters.
- **8,690 entries** in `importArts`.
- **7,215,777 bytes** of JSON.
- Empty `dynlibs` and `plugins` lists.

This is dependency setup, not recompiling Mathlib. The measured standalone command
explicitly disabled building and cache downloads:

```sh
cd v4.33.1-optimized/playground
/usr/bin/time -p lake setup-file Playground/Scratch.lean --no-build --no-cache \
  > .lake/setup-file-probe.json
```

Observed: `real 10.03`, `user 2.70`, `sys 5.83` seconds. This is one measurement,
not a repeated median. The high system time is a reason to investigate operating
system calls, not proof of a particular filesystem bottleneck.

Relevant source files in the local Lean checkout under
`playground/.lake/toolchains/lean4/`:

- `src/Lean/Server/FileWorker/SetupFile.lean`: `runLakeSetupFile`, `setupFile`.
- `src/lake/Lake/CLI/Serve.lean`: `setupFile`.
- `src/lake/Lake/Build/Module.lean`: `setupEditedModule`, `setupServerModule`.

## Direct language-server probe

The probe used the optimization repository's Python `LeanLsp` client to launch an
independent `lake serve`, initialize with widgets enabled, open the exact scratch
file with dependency building disabled, wait for empty `$/lean/fileProgress`, and
request `$/lean/plainGoal` at line 4, column 3 (zero-based position 3:2).

| Configuration | Initialize + open/check | Goal request after completion |
| --- | ---: | ---: |
| Normal optimized configuration | 14.3905 s | 0.00847 s |
| `LEAN_TACTIC_INDEX=0` | 16.4806 s | 0.00280 s |

In the normal trace initialization completed at 0.919 s, giving approximately
13.472 s from `didOpen` to finished processing. Both configurations returned the
correct goal:

```lean
x y : ℝ
h : x < y
⊢ (x + y) / 2 < y
```

These are single diagnostic runs, not a controlled editor benchmark suite. They
bypass Cursor and its Infoview rendering, but reproduce a substantial opening
delay. Disabling the tactic image did not remove that delay.

Local, ignored investigation artifacts (not durable across deleting `.lake`):

- `playground/.lake/probe-editor.py`
- `playground/.lake/lsp-probe-normal/lsp-trace.jsonl`
- `playground/.lake/lsp-probe-normal/server.stderr.log`
- `playground/.lake/lsp-probe-no-image/lsp-trace.jsonl`
- `playground/.lake/lsp-probe-no-image/server.stderr.log`
- `playground/.lake/setup-file-probe.json`

## Other observations; avoid overinterpreting them

Several different PIDs were observed for Cursor's scratch-file worker while its
watchdog stayed alive. This demonstrates worker replacement, but its cause was
not established: it could have been manual restarts, import edits, or another
trigger. No automatic crash loop was demonstrated.

A two-second `sample` of one worker showed its main loop waiting for LSP messages
and task workers idle, rather than executing proofs. That sample describes one
moment after startup; it does not prove that Cursor's UI was stuck or establish
the cause of the earlier wait. The temporary sample was saved as
`/tmp/lean-worker-sample.txt`.

The installed extension defaults `lean4.infoview.debounceTime` to 50 ms after
cursor movement. Lean's `server.reportDelayMs` defaults to 200 ms for progress and
diagnostic reporting after edits. These are different delays, not an explanation
for the measured multi-second file opening.

## Upstream reports and fixes

Searched the web and GitHub issue/PR APIs on 2026-09-11. These are related reports;
none proves the exact cause of this machine's 10-second setup measurement.

1. **[Lean issue #8092](https://github.com/leanprover/lean4/issues/8092)**,
   opened April 24, 2025, still open when checked. Reports 80,000–150,000 filesystem
   calls around importing Mathlib, including repeated failed artifact-path lookups.
   It describes major slowdowns on slow/networked storage and under high concurrency.
   This is a relevant hypothesis to investigate, not a measured syscall count for
   our setup.

2. **[PR #8736](https://github.com/leanprover/lean4/pull/8736)**,
   merged June 12, 2025. Partially rolled back `lean --setup` integration because
   of a significant Lake build-performance regression.

3. **[PR #8787](https://github.com/leanprover/lean4/pull/8787)** investigated setup
   integration performance. The maintainer closed it on April 12, 2026, saying it
   had been solved by **[PR #9053](https://github.com/leanprover/lean4/pull/9053)**.
   That PR, merged July 16, 2025, pre-resolves transitive module artifacts and
   explicitly acknowledges that resolving transitive imports retains a reduced
   performance penalty.

4. **[PR #10052](https://github.com/leanprover/lean4/pull/10052)**,
   merged August 25, 2025, fixes a blocking `lake setup-file` call escaping its
   dedicated server task. The reported symptom was server processes surviving
   VS Code shutdown. This is a process-handling fix, not removal of setup work.

GitHub commit comparisons confirmed that both relevant merged fixes are already
ancestors of `v4.33.1` (zero commits behind):

| PR | Merge commit |
| --- | --- |
| #9053 | `180bfeaba42c9261103bdcf983ca40a95e83792c` |
| #10052 | `be4651a77285841c00ee80a5cd9ff416811179fd` |

Therefore simply applying those old fixes will not solve this case. The search
did not identify a confirmed newer drop-in fix for this particular delay; this
is not a claim that no such fix or discussion exists.

## Next investigation steps

1. Repeat `lake setup-file` under stock and optimized v4.33.1 against identical
   cached dependencies. Select the matching runtime libraries explicitly to avoid
   accidentally measuring stock code inside the fork or vice versa.
2. Profile the setup process itself, including filesystem-call counts/time and
   CPU stacks. Separate workspace loading, artifact validation, dependency graph
   traversal, and JSON generation before choosing a fix.
3. Use repeated LSP opening tests as the success criterion, not just bare
   `lean Scratch.lean` timings. Keep initialization, setup, import/checking, and
   goal-response latency distinct.
4. If testing cached setup results, first establish correct invalidation for
   changed headers, Lake configuration/manifests, and dependency artifacts. A
   blindly reused setup response could silently select stale project state.
5. Preserve the user's constraint: no Mathlib rebuild/native tactic compilation.
