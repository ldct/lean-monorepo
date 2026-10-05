# Lean Setup Cache (Experimental)

This companion extension adds an opt-in, project-local cache for the Lean 4 VS Code extension's Lake setup-file requests. It uses the project-selected Elan toolchain and normal Lake server arguments; it does not modify Lean, Mathlib, or a global Elan configuration.

## Requirements

- VS Code with [Lean 4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
- A trusted, local **single-folder** Lean project containing `lean-toolchain` and `lakefile.toml` or `lakefile.lean`
- macOS or Linux, with Python 3.9 or newer and `fcntl`

Multi-root and virtual workspaces are intentionally unsupported because the Lean extension applies its PATH extensions to the whole window.
The bundled runtime has been tested with Lean v4.33.1; other versions have not yet been validated.

## Use

1. Install the VSIX with **Extensions: Install from VSIX**.
2. Open the Lean project itself as the only workspace folder.
3. Run **Lean Setup Cache: Enable for Workspace**, then restart the Lean server.

Enable installs the launcher under `.vscode/lean-setup-cache/` and adds only its relative `lean4.envPathExtensions` entry. It preserves existing entries. **Lean Setup Cache: Disable for Workspace** removes the entry it owns; restart the Lean server after either change.
After updating this extension, run **Enable for Workspace** again to refresh the copied project-local runtime.

**Lean Setup Cache: Show Status** writes enablement, cache-hit telemetry, and validator results to the *Lean Setup Cache* output channel. **Lean Setup Cache: Clear Workspace Cache** advances the cache generation so subsequent setup requests refill it. It does not delete old files while a server may still use them.

## Behavior and limits

The first setup response fills the cache and records dependency/build-tree metadata, so it can be slower than ordinary Lake setup. Later cache hits return immediately while validation runs in the background. Validation detects metadata changes, additions, deletions, and replacements in the selected project artifacts and dependencies; it invalidates future workers when it finds a change.

The worker that already received a cached setup response can remain stale after a background invalidation. Restart that worker manually before relying on changed dependencies. Clear the cache after a toolchain or dependency/artifact change when you need an immediate refill. The validator uses metadata rather than content hashes, so it is an experimental acceleration rather than a substitute for a clean rebuild.

This extension is an experimental prerelease. It contains no telemetry or account credentials. Disable caching before uninstalling so the workspace PATH setting is removed.
