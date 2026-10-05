# VS Code Infoview follow-up — 2026-09-11

**Current installation:** filesystem validation was subsequently removed at the
user’s request. Historical validated-cache measurements below describe the prior
implementation. Cache keys, configuration checks, and output integrity checks
remain; dependency/artifact changes require manually clearing cached responses.

The 7.2 MB JSON response is **not** the main cause of the delay. Repeated Lake
dependency setup takes seconds; JSON serialization/writing and parsing together
took about 0.09 seconds in a native phase probe. A validated local setup cache
reduced warm file-opening time from **7.81 to 4.48 seconds** (three-run medians,
43% reduction). It does not make importing all of Mathlib instantaneous.

This follow-up ran on an **Apple M1 Max, 64 GiB RAM, macOS 26.4.1**, with VS Code
and `leanprover.lean4` 0.0.239. The earlier Cursor notes describe a different M5
Max machine; their timings must not be combined with these as one benchmark.
The optimized compiler, pinned dependencies and standard Mathlib cache are the
ones documented in `playground/README.md`. No Mathlib/native-tactic rebuild was
performed.

## Where the time goes

A native executable importing Lake's existing implementation called
`loadWorkspace` and `setupServerModule`, then serialized/wrote the resulting
`ModuleSetup` and parsed it back into Lean's `ModuleSetup` type:

| Phase | Time, single diagnostic run |
| --- | ---: |
| Find installation and construct configuration | 0.043 s |
| Load workspace | 0.709 s |
| Resolve/check dependency setup | 4.335 s |
| JSON serialization plus file write | 0.039 s |
| JSON parse and decode to `ModuleSetup` | 0.053 s |

The response still contains 8,690 entries and 7,215,777 bytes (including Lake's
trailing newline). The serialization/write timing is combined deliberately:
Lean can move pure computation across intermediate timestamp calls. It does not
establish separate `toJson` and `compress` timings, nor measure pipe transfer.

A 3-second macOS `sample` of actual `lake setup-file` frequently stopped in
`read`, `open`, `stat`, and task waits under Lake's dependency traversal. This
supports investigating filesystem work; it is not an exact syscall count or a
complete allocation of setup time. The trace does not establish one specific
OS/filesystem defect.

Exploratory thread-count tests were unhelpful as a main fix: one thread took
about 19.5 s, two 11.1 s, four 6.7–7.0 s, and the default ten about 5.6 s in that
batch. Later trials with 32/64 threads took 4.59/4.45 s. These were not the final
controlled LSP comparison, and no global thread setting was changed.

Two alternating setup runs with the stock and optimized runtimes against the
same project/artifacts gave 3.94/3.74 s stock and 4.26/4.30 s optimized. All four
responses had identical SHA-256
`6509aea3bd8b4e3efb9e34b8bdab8f6fb2a9a60144f9ef33b6088c992992b7f0`.
This setup overhead exists with stock Lake too.

## Does eliminating setup actually help the server?

A diagnostic-only replay supplied the same full JSON to an independent Lean
server, with unchanged files/dependencies. Direct-server opening took 3.54 s with
replay versus 8.78 s with normal Lake setup. Both returned the correct goal.
The replay was **not installed in VS Code**: it has no invalidation and would be
unsafe as a general development workflow. Its purpose was to measure the benefit
available from avoiding repeated setup while retaining the large JSON.

The installed implementation instead validates state before reusing a response.
Final measurements alternated normal setup and cache hits, using `lake serve`,
widgets enabled, `dependencyBuildMode = never`, the identical on-disk scratch
file, and a new server for each run. Completion means an empty
`$/lean/fileProgress`; every run additionally checked for errors and requested
the actual goal at line 4, column 3.

| Run | Normal setup: open to checked | Validated cache: open to checked |
| --- | ---: | ---: |
| 1 | 8.0698 s | 4.4529 s |
| 2 | 7.7228 s | 4.4763 s |
| 3 | 7.8121 s | 4.4774 s |
| **Median** | **7.8121 s** | **4.4763 s** |

Initialization is excluded from those columns and was about 0.84/0.82 s.
Median subsequent goal requests were 3.34/2.85 ms. These measurements bypass
VS Code rendering: they measure the server delay that the editor waits for,
not a pixel-to-pixel GUI benchmark. A final cache-hit validation scanned about
175,670 files in 1.50 s; Mathlib import/checking remains after that.

The live VS Code window was also restarted twice. Its second request recorded a
cache hit with 1.28 s validation, and Infoview displayed `No goals` and `Goals
accomplished!` for the `ring` example with no processing indicator or problems.
The optimized project's cache is left enabled.

The first cache-populating opening in the final batch took 10.89 s. A miss is
slower than ordinary setup because of the validation scans. Expect this after
dependency changes; the improvement applies to repeated openings/restarts with
unchanged setup inputs. Ordinary proof-body edits in the edited file can reuse
setup; their complete parsed import header remains part of the key.

## Installed local workaround and its boundaries

`playground/scripts/editor-setup-cache.py` wraps only this optimized toolchain's
`bin/lake`; the real executable is retained as `bin/lake.real`. All ordinary Lake
commands pass through. It only caches editor `setup-file <Playground file> -`
requests with the supported flags.

- Cache keys include the file path, full stdin header (including unsaved imports),
  arguments, and a hash of the process environment. Raw environment values are
  not written to the cache or diagnostic record.
- Every reuse scans the local sources, build outputs, installed compiler/core
  artifacts/source, and Git metadata. File identity, permissions, size, mtime and
  ctime are checked; directory contents detect additions/removals/renames.
- The edited file's proof body is excluded because Lake receives its parsed
  header on stdin. Dependency source files are not excluded.
- Configuration/manifests/toolchain files are content-locked at installation.
  Changes disable caching until reinstall. External symlinks/search paths,
  dynamic-library/plugin setup results, and unsupported flags bypass the cache.
- A miss invokes normal Lake. Only successful results with unchanged before/after
  snapshots are stored, atomically. Failures are not cached. Corrupt entries
  cause normal setup. Metadata validation has the usual filesystem concurrency
  limits; it is not a transactional snapshot against concurrent writers.

This is an experimental workaround for this pinned, local project, not a
general upstream solution for arbitrary Lake configurations with external or
nondeterministic inputs. It deliberately keeps normal rebuild/invalidation
paths available. A robust upstream persistent workspace/dependency service could
avoid more work than this conservative full metadata scan.

Thirteen isolated tests cover cache hits, proof-body versus dependency edits,
unsaved headers, writes preserving mtime, add/remove/rename, configuration and
environment changes, corrupt entries, failed setup, mutation during setup, and
unsupported paths/flags. A real LSP test also changed an unsaved import to a
nonexistent module and confirmed that the server reported the new error.

## Reproduce or disable

From `v4.33.1-optimized/playground`:

```sh
python3 scripts/install-editor-cache.py
python3 scripts/test-editor-setup-cache.py
python3 scripts/probe-editor.py warmup
LEAN_EDITOR_SETUP_CACHE=0 python3 scripts/probe-editor.py baseline
python3 scripts/probe-editor.py cached

# Restore the real Lake executable, then restart the file in the editor.
python3 scripts/install-editor-cache.py --disable
```

The most recent eligible request is recorded in
`.lake/editor-setup-cache/last-request.json` (`hit`, validation/operation time,
file count and PID). `LEAN_EDITOR_SETUP_CACHE_VERBOSE=1` additionally emits
diagnostic messages; leave it off for normal editing.

For native phase timings (not `lean --run`, which cannot execute all of Lake's
imported configuration machinery here):

```sh
mkdir -p .lake/infoview-investigation
lake env lean -c .lake/infoview-investigation/ProfileSetup.c scripts/ProfileSetup.lean
lake env leanc -leanshared -O3 \
  -o .lake/infoview-investigation/profile-setup \
  .lake/infoview-investigation/ProfileSetup.c \
  "-Wl,-rpath,$PWD/.lake/toolchains/lean4/build/release/stage2/lib/lean"
lake env .lake/infoview-investigation/profile-setup
```

Raw local probes, setup samples, protocol traces and results are under the ignored
`.lake/infoview-investigation/` directory. The final numbers above are retained
here so the result survives deleting `.lake`.

## Follow-up: what remains after setup

The 3.54-second replay measurement includes worker startup, importing Mathlib,
and elaborating the scratch examples. It is not a separately measured pure
import phase or an established lower bound.

A fresh same-machine import-only comparison used each toolchain's own runtime
and core oleans, the same cached Mathlib artifacts, one warmup per configuration,
and two alternating measured runs. Stock: 4.7838 / 4.7064 seconds; optimized:
3.4470 / 3.3233 seconds (about 29% lower mean). Diagnostics were identical and
empty. RSS was approximately 5.69 GB stock versus 1.50–1.71 GB optimized.
Raw results: `playground/.lake/infoview-investigation/import-comparison-isolated.json`.
This does not reproduce the release README's M2 Pro 10.2 → 2.3 second speedup.
The reason for the different speedup has not yet been established.

Optimized diagnostics confirm a lazy-parts cache hit and a tactic-image hit
covering 93 extensions. Import-only diagnostics still report 1,132 IR-module
loads and 8 private-part loads. Laziness does not eliminate executable machinery
needed by initializers. Reading Lean's importModulesCore/finalizeImport code
shows remaining artifact discovery/mapping, constant and module lookup-table
construction, and persistent-extension initialization. It does not recheck every
imported Mathlib proof.

A two-second sample near the beginning of optimized import captured both
importModulesCore and finalizeImport, with frequent stat/open/mmap work and
hash-table construction. This is a partial sampling window, not an exact timing
breakdown of the whole import. The release's tactic-image documentation explicitly
leaves parserExtension and other closure-containing states uncached; its own
measurements report about 380 ms for parserExtension, not a measurement on this
machine.

The release's sub-second fork-worker result is a separate Linux-only loader-reuse
experiment, not a benefit automatically installed by the ordinary compiler patch.
Snapshot reuse is also a separate path. Further import optimization may help;
these measurements do not establish that a major architectural rewrite is the
only possible route below one second.

## Experiment: skip the cache validation scan

Temporarily bypassed the filesystem snapshot on existing cache entries, keeping
request/environment keys, configuration checks and output integrity checks.
The experiment flag was excluded from the cache key so both modes used the same
entry. After one cache-populating warmup, alternated three runs per mode with
fresh language servers and the same goal/diagnostics assertions as above.

| Median | Validated | No filesystem validation |
| --- | ---: | ---: |
| Server initialization | 0.861 s | 0.833 s |
| File open to checked | 4.652 s | 3.185 s |
| Cache handler | 1.483 s | 0.027 s |
| Goal request | 0.003 s | 0.003 s |
| Total server path (median of per-run totals) | 5.494 s | 4.017 s |

Skipping validation saves about 1.47 seconds of opening latency (31.5%), closely
matching the removed scan. All six measured runs hit the cache; unchecked runs
scanned zero files. JSON handling remains. VS Code rendering is not measured.
The original validation implementation was restored after the experiment; no
persistent bypass option was retained. Restoring the script changes its metadata,
so the next validated request may repopulate its cache.
Raw results: `playground/.lake/infoview-investigation/validation-experiment.json`.

## Installed change: validation removed

Deleted the filesystem snapshot traversal and pre/post-setup comparisons. The
existing installed Lake wrapper picks up this change directly. Updated the cache
tests and playground README; all 13 tests pass. A real LSP probe returned the
correct goal without diagnostics and recorded a cache hit in 0.016 seconds with
zero scanned files. That single check took 4.136 seconds from open to checked;
it confirms operation, not a replacement for the alternating experiment above.

## Detailed import phase profiling

See [IMPORT-PHASE-PROFILE.md](IMPORT-PHASE-PROFILE.md) for direct phase timers,
stock comparisons, editor artifact-map measurements, and whole-import samples.
Editor-map import: about 0.67 s module loading, 0.80 s environment construction,
and 1.13 s extension initialization (parser alone about 0.56 s).
