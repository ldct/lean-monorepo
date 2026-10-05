# Lean 4.33.1 optimized playground

This has the same layout and Lake options as `v32/playground`: `Playground.lean`
imports files under `Playground/`, and the default build target is `Playground`.

```sh
cd v4.33.1-optimized/playground
lake build
lake env lean Playground/Scratch.lean
```

The local elan toolchain `lean-v4.33.1-optimized` uses
[danromik/lean-optimizations](https://github.com/danromik/lean-optimizations)
at `d06e784fc4e9e031ea4db91d706edbcef287a141`, applied to Lean v4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). Mathlib is pinned to v4.33.1
(`0df444a360eaa60ab8c11dca51a86af692955474`) in the Lake manifest.

**Mathlib uses the standard downloaded cache, without a source rebuild or native
tactic compilation.** The runtime address reservation, no-touch reference counts,
and lazy part loading work with that cache. Search and tactic indexes are generated
separately under `.lake/optimization-cache`, and a toolchain wrapper enables them
for ordinary Lake commands and editor workers. The shell-first layout and stored
search entries in Mathlib's oleans are not enabled; those require rebuilding Mathlib.

## Reproduce the setup

Apple Silicon macOS is required by this setup script. Install elan, CMake, a C/C++
compiler, GMP, libuv, and pkgconf, then run:

```sh
./scripts/setup.sh
```

The setup builds Lean stage 2 with the macOS performance patch and the separate
`fix-codegen-meta-initialize.patch` (included during the initial Lean build).
It downloads Mathlib's cache, builds only the playground, and warms the indexes.
Source checkouts and generated artifacts live under the ignored `.lake/` directory.
The first Lean build takes substantial time and disk space.

To confirm which compiler Lake is using:

```sh
lake env printenv LEAN_SYSROOT
LEAN_LAZY_PARTS_VERBOSE=1 LEAN_TACTIC_INDEX_VERBOSE=1 lake env lean scripts/Import.lean
```

The sysroot must end in this project's `.lake/toolchains/lean4/build/release/stage2`.
`lean --version` deliberately matches stock Lean so released artifacts remain
compatible; it does not establish that the optimized compiler is running.

These upstream optimizations are experimental. Indexes are keyed by the import
closure and configuration. Other imports still work, but the first use can be
slower while the lazy/search caches warm. A command-line tactic-index image does
not necessarily match an editor worker's configuration. Removing `.lake/` also
removes the linked compiler; rerun setup before using this project again.
Existing version directories and their toolchains are independent.

## Editor setup cache

The local Infoview investigation found that repeatedly resolving/checking the
dependency graph costs seconds; serializing and parsing its 7.2 MB JSON costs
about a tenth of a second. An experimental, project-local cache can avoid the
repeated graph work:

```sh
python3 scripts/install-editor-cache.py
```

It wraps only this optimized toolchain's Lake executable. Editor `setup-file`
requests for files in `Playground/` reuse successful responses without scanning
sources, artifacts, the compiler, or Git metadata. The parsed header (including
unsaved imports), file path, arguments, and environment remain cache keys.
Dependency edits, artifact changes, additions, removals, and renames do not
invalidate entries. After such changes, clear the stored responses:

```sh
find .lake/editor-setup-cache -name '*.json' ! -name configuration.json -delete
```

The installer locks package configurations/manifests by content. Changes to those
still bypass caching until reinstalling; clear stored responses before reinstalling.
External Lean search paths, dynamic libraries/plugins, and custom setup flags
bypass caching. Normal Lake commands and builds still perform their usual checks.

Skipping filesystem validation reduced measured file-open time from 4.65 to
3.19 seconds. Mathlib import time remains. Request diagnostics are recorded in
`.lake/editor-setup-cache/last-request.json`; `files: 0` reflects the removed scan.

```sh
# Restore the original Lake executable (also use before rebuilding Lean).
python3 scripts/install-editor-cache.py --disable
# Or bypass caching for one process and its children:
LEAN_EDITOR_SETUP_CACHE=0 lake serve
# Run cache tests and an actual LSP opening probe:
python3 scripts/test-editor-setup-cache.py
python3 scripts/probe-editor.py warm
LEAN_EDITOR_SETUP_CACHE=0 python3 scripts/probe-editor.py baseline
```

The probe records timings and protocol traces under `.lake/infoview-investigation`.
Restart the file in VS Code after installing or disabling the wrapper.

## Benchmarks

See [BENCHMARKS.md](BENCHMARKS.md) for the measured results on this machine.
See [the editor startup investigation](../EDITOR-STARTUP-INVESTIGATION.md) for
Cursor/Infoview measurements, the slow `lake setup-file` step, and upstream issues.

```sh
python3 scripts/benchmark.py --repeat 5
```

By default both compilers read this project's same standard Mathlib cache, with
each compiler using its own core oleans and runtime libraries. Install stock Lean
with `elan toolchain install leanprover/lean4:v4.33.1` if needed. The optional
`--stock-project PATH` selects a different cached Mathlib v4.33.1 project.
`.lake/stock` also preserves a separate copy of the initial downloaded packages.

Each case is warmed before timing. Timed runs alternate order and compare stock,
optimized, and optimized with the runtime switches disabled. Every run must
succeed and produce identical stdout/stderr. The JSON report contains raw runs
and medians for elapsed time, CPU time, and maximum resident memory. These are
warm process benchmarks, not cold-cache or editor-latency measurements; RSS includes
shared mapped pages. The disabled arm still uses stage 2's rebuilt core oleans,
so it is an ablation control rather than a byte-identical stock installation.
