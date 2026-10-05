# Project-local editor setup-cache launcher

`project-setup-cache.py` and `serve-with-setup-cache.py` provide an opt-in
cache for the expensive Lake `setup-file` request made while a Lean editor worker
opens a file. They do not replace an Elan binary, alter the active optimized
toolchain, rebuild Lean, Mathlib, or native tactics, or enable any snapshot code.

The launcher derives the chosen toolchain's own `LEAN_PATH`, sysroot, and runtime
environment through that toolchain's real Lake executable. It then starts the
real Lean language server with only `LAKE` redirected to the project-local shim.
The shim caches successful editor `setup-file` responses under a toolchain-named
directory in `.lake/`. Normal Lake commands and builds are passed to real Lake.

## Start a stock server

From this playground, after installing stock Lean if necessary:

```sh
elan toolchain install leanprover/lean4:v4.33.1
python3 scripts/serve-with-setup-cache.py --toolchain leanprover/lean4:v4.33.1
```

To launch the separate stock playground without changing this playground's
`lean-toolchain`, select it explicitly:

```sh
python3 scripts/serve-with-setup-cache.py --project ../../v4.33.1/playground --toolchain leanprover/lean4:v4.33.1
```

This is deliberately an explicit launcher, so it is reversible and does not
modify global Elan state. Use it as the server command in an LSP test client or
other local integration that can launch the server command. To launch the same
selected server without the cache:

```sh
python3 scripts/serve-with-setup-cache.py --toolchain leanprover/lean4:v4.33.1 --disable
```

For VS Code, open [the stock opt-in workspace](../../../v4.33.1/playground/.vscode/opt-in-setup-cache.code-workspace)
(or [the optimized opt-in workspace](../.vscode/opt-in-setup-cache.code-workspace))
instead of changing the normal monorepo workspace. It uses the extension's
supported `lean4.envPathExtensions` setting. The project-local `lake` command
handles the extension's exact `lake [+toolchain] serve -- <project>` entry point
and starts the selected Lean server through this launcher, with the cache shim
already in `LAKE`. It passes non-server Lake commands through to the selected
real Lake. Close the opt-in workspace and reopen the usual one to disable it;
no global Elan binary or active normal-workspace configuration changes.

The stock workspace was exercised with the extension command shape
`lake +leanprover/lean4:v4.33.1 serve -- /…/v4.33.1/playground`: after a normal
fill, the next launch had a fresh setup-cache hit in 0.013 s and returned the
Scratch plain goal in 4.089 s. The selected project and stock toolchain were
forwarded unchanged.

## Cache contract

The cache key includes the file path, parsed unsaved header/imports, setup
arguments, and environment. Package and project configuration contents are
locked at initialization and configuration edits disable hits. It intentionally
does **not** block a hit on validation: it returns the cached response, flushes
the protocol stream, then schedules a detached validator. An advisory lock allows only one scan
at a time, and completed scans throttle subsequent checks for 60 seconds. The
validator records metadata and directory membership for `.lake/build` and pinned
`.lake/packages`; additions, deletions, replacement, size, mtime, ctime, and
inode changes advance the cache generation so later requests miss. It does not
hash contents, scan editable `Playground` source text, scan Git metadata, or
restart a current worker. A change found after a hit means that current worker
may still use its already-returned setup; restart it manually to pick up the
invalidated dependency state.

For known dependency changes, clear the cache before restarting to avoid even
one optimistic stale hit. Manual clearing is required for toolchain changes in
place and changes outside the scanned trees:

```sh
find .lake/editor-setup-cache-leanprover_lean4_v4.33.1 -name '*.json' ! -name configuration.json -delete
```

After editing `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, or package
configuration, clear the entries with the same command; the launcher refreshes
the configuration lock on its next start. `LEAN_EDITOR_SETUP_CACHE=0` bypasses
the shim for a process and its workers.

The baseline is captured before and after a cache fill; only a stable tree and
unchanged generation can be cached. Baselines are immutable sidecars, so hits do
not parse the large file inventory. Initial fills therefore pay for two scans.
Symlinked dependency directories or scan failures prevent creating a cache entry.
This implementation uses Unix advisory locks (macOS/Linux).

`LEAN_SETUP_CACHE_BACKGROUND_VALIDATE=0` disables background checks.
`LEAN_SETUP_CACHE_VALIDATE_INTERVAL=0` forces a check on every hit for testing.
`validation.json` records scan start, completion, duration and outcome; detected
changes also produce a warning on the next setup request. No automatic worker
restart occurs. Checks are triggered by setup requests, not continuous polling.

## Earlier measurements before background validation

The actual stock project `v4.33.1/playground/Playground/Scratch.lean` already
has a `module` header. A real stock v4.33.1 server opened that unmodified text
with correct plain goals in this one-pair check:

| configuration | Server startup | Document open |
| --- | ---: | ---: |
| stock project, cache disabled | — | 8.915 s |
| stock project, cache fill | — | 8.093 s |
| stock project, cache hit | — | 3.808 s |

The open column ends at the file-progress completion event, so it is server
protocol timing and does not claim GUI/Infoview rendering latency. The hit has
fresh telemetry from its own request (`hit: true`, 0.013 s, zero validation
files); it is not stale cache state. The separate optimized-project benchmark
uses an unsaved leading `module` header without editing Scratch, and verifies
plain and interactive goals, proof-error and recovery, and unsaved
missing-import and recovery behavior.

Reproduce with:

```sh
python3 scripts/benchmark-module-setup-cache.py --toolchain leanprover/lean4:v4.33.1 --repeat 3
```

It writes raw traces and JSON under ignored `.lake/infoview-investigation/`.

Independent review: the stock VS Code command shape passed plain and interactive
Infoview goals, proof error/recovery, missing-import/recovery, and moved-header
checks. A repeated opening took 4.024 s with fresh setup-hit telemetry (~0.013 s).
Both Scratch files retained their original hashes. This verifies the protocol
entry point, not a GUI rendering benchmark.

## Background-validation comparison (2026-09-11)

Independent review ran three alternating opens per mode on the actual stock
project, preserving its existing `module` Scratch. Every cached run asserted a
fresh setup hit; every checked run forced a real scan and asserted successful
completion. All runs requested plain and interactive Infoview goals.

| Mode | Median document open |
| --- | ---: |
| No setup cache | 7.944 s |
| Cache, background validation disabled | 3.828 s |
| Cache, background validation running | 4.233 s |

The checked cache saved 3.711 s (47%) against uncached opening in this batch.
Scanning added 0.405 s versus unchecked caching through resource contention,
although the setup response itself still took ~0.013 s. Background scans took
2.18–2.20 s and completed during file opening. Default 60-second throttling means
not every opening incurs that scan. A fresh cache fill took 12.717 s because it
also establishes and verifies the baseline; initialization took ~0.9–1.0 s
separately. These are protocol timings, not GUI rendering measurements.

Reproduce from this playground:

```sh
python3 scripts/benchmark-background-setup-cache.py --repeat 3
python3 scripts/test-project-setup-cache.py
```

The benchmark writes fresh traces and results to the stock project's ignored
`.lake/infoview-investigation/background-review-<timestamp>/` directory.
Reviewed run: `background-review-1789116634869718000/results.json`.
