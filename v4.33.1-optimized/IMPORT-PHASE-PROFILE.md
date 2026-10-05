# Import phase profiling — 2026-09-11

Machine: Apple M1 Max, 64 GiB RAM, macOS 26.4.1. Same pinned Mathlib cache and
optimized toolchain as the Infoview investigation. No Mathlib rebuild, active
compiler replacement, or validation re-enablement was performed.

## Editor-relevant breakdown

A standalone native Lean probe invokes the real `importModulesCore` and
`finalizeImport` functions, with initializers enabled, `leakEnv=true`, and the
same legacy `import Mathlib` as Scratch. It can decode the saved editor ModuleSetup
and pass its artifact map to the importer. The noext mode omits extension loading
as a diagnostic ablation, not a usable editor configuration.

| Phase | Warm seconds | Method |
| --- | ---: | --- |
| Decode supplied ModuleSetup and initialize probe | 0.069–0.071 | Direct timestamp |
| Load modules with editor artifact map | 0.656–0.681 | Direct timestamp, two full runs |
| Construct environment without extension loading | 0.791–0.802 | Direct timestamp in two noext runs |
| Incremental extension-loading cost | approximately 1.13 | Full finalization mean 1.931 minus noext mean 0.796 |
| Full finalization including extensions | 1.923–1.939 | Direct timestamp, two full runs |

Thus module loading plus finalization accounts for approximately 2.60 seconds.
This does not include process startup, server protocol, setup-cache handling,
checking the scratch examples or GUI rendering. It is not an exact additive
partition of the earlier 3.185-second LSP-open measurement. The native full probes
had wall times 3.45 and 2.99 seconds; startup variation lies outside the timed
import phases. The previous repeated LSP experiment is the better end-to-end
measurement: 3.185 s file-open, 4.017 s including server initialization and goal.

## Extension detail

The probe wraps the addImportedFn callbacks registered before import, preserving
names and semantics. It does not individually time extensions registered later
by imported initializers, or runInitAttrs itself. All extension-related work is
included in the full/noext phase difference. Cache diagnostics separately confirm
the lazy-parts index hit and tactic image hit (93 extensions, mmap=true).

| Timed handler with editor map | Milliseconds, single diagnostic run |
| --- | ---: |
| Lean.Parser.parserExtension | 557.7 |
| Lean.Elab.macroAttribute | 34.2 |
| Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute | 19.8 |
| Lean.PrettyPrinter.Delaborator.delabAttribute | 7.9 |
| Lean.Elab.Tactic.tacticElabAttribute | 5.4 |

Parser initialization reconstructs parser entries and evaluates parser constants,
often through the IR interpreter. It is not covered by the tactic image. The
remaining approximately 0.57 s beyond the parser includes other handlers, imported
initializers, image handling and extension bookkeeping; it is not separately
attributed by direct timers here.

## Same-machine stock comparison

Each executable was compiled against its own toolchain and ran with its own core
oleans/runtime, using the same Mathlib artifacts. These command-line-style probes
do not use the editor artifact map. First full run discarded as warmup (stock was
20.14 s cold); two alternating warm runs reported below.

| Phase | Stock | Optimized |
| --- | ---: | ---: |
| importModulesCore | 2.225–2.302 s | 1.151–1.203 s |
| Full finalizeImport | 2.258–2.263 s | 1.914–1.977 s |
| finalizeImport without extensions | 0.847–0.859 s | 0.786–0.792 s |
| Incremental extension cost, difference of means | 1.408 s | 1.156 s |
| Full process | 4.730–4.790 s | 3.403–3.534 s |

Most of the measured improvement is in loading modules. Initial extension callback
probes show stock simp rebuilding at 247 ms and instances at 68 ms, absent from
optimized callbacks because their image is used. Parser remained 407 ms stock vs
571 ms optimized in one diagnostic run; this suggests a possible deferred-loading
tradeoff, but does not establish its cause. We have not explained the release's
larger M2 Pro stock baseline or reproduced its overall speedup.

## Whole-import samples and opportunities

macOS sample captured the actual stock and optimized `lean scripts/Import.lean`
processes through exit, starting shortly after launch (not all startup).
The optimized import thread had 2,730 import samples. Frequent leaf frames were
stat (438), open (237), persistent-address-range checks (160), constant hash-map
insertion (108), and marking persistent objects (104). Dynamic-loader symbol
lookup (`dyld4::APIs::dlsym`) appeared in 506 inclusive samples, approximately 19%
of captured import samples. These are sample counts, not exact milliseconds or
syscall counts; inactive helper-thread waits must not be added to them.

The parser stacks include mkParserOfConstantUnsafe, lean_eval_const and interpreter
loading/evaluation. Dynamic symbol lookup work overlaps parser/initializer time:
it must not be added as a separate phase. Source ir_interpreter.cpp already has a
process-local cache for native-symbol lookup successes and failures. Candidate
improvement: avoid initial native lookups known to be unavailable, using a complete
loaded-symbol/module inventory, or preserve this information with the loaded
worker. Any implementation must respect plugins and native code availability.

Priority opportunities:

1. Parser/initializer restoration or reducing first native-symbol lookup work.
   Parser alone is about 0.56 s; all extension initialization about 1.13 s.
2. Avoid rebuilding constant/module maps and extension-entry structures: the
   non-extension finalization phase is about 0.80 s, including lazy-index work and
   persistent marking, not exclusively hash-table construction.
3. Reduce remaining module opens/maps/metadata work: about 0.67 s with editor
   artifact paths already supplied. Command-line path discovery costs more and
   should not be mistaken for the editor's remaining cost.
4. Reusing an already-loaded worker avoids multiple stages together. Savings from
   individual changes above are unmeasured; no single measured phase alone explains
   all of the remaining delay or guarantees sub-second startup.

## Reproduction and artifacts

Durable probe: `playground/scripts/ProfileImport.lean`.
Compile with the relevant toolchain's lean -c, then leanc -leanshared -O3 and its
lib/lean rpath (linking static Lean together with the shared library is invalid).
Use that toolchain's LEAN_SYSROOT and core LEAN_PATH, plus the project's package
paths. For optimized runs set the search/tactic cache directories as in
scripts/benchmark.py. PROFILE_IMPORT_SETUP points at the saved setup.json.
Arguments: full, noext, or extensions.

Raw data under playground/.lake/infoview-investigation:
- phase-benchmark.json and phase-*-*.stderr: stock/optimized phase comparison.
- phase-editor.json and phase-editor-[1-5].stderr: supplied editor artifact map.
- phase-cache-diagnostics.stderr: confirmed cache usage.
- full-import-{stock,optimized}.sample.txt: actual lean executable samples.
- phase-benchmark.py, phase-editor.py, sample-full-import.py: orchestration scripts.

The editor cache still has filesystem validation removed as requested.
