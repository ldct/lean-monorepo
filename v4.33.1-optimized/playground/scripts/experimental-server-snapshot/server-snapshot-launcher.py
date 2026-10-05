#!/usr/bin/env python3
"""Validated launcher for the isolated Lean file-worker snapshot experiment.

The manifest is intentionally project-specific.  Validation failure always starts the
experimental server without LEAN_SERVER_SNAPSHOT, leaving FileWorker on its ordinary path.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[2]
HERE = PROJECT / ".lake/infoview-investigation/parser-environment"
PREFIX = HERE / "lean4-server-snapshot/build/release/stage2"
LEAN = PREFIX / "bin/lean"
SNAPSHOT = HERE / "server-scratch.snap"
SETUP = HERE / "clone-setup.json"
MANIFEST = HERE / "server-scratch.manifest.json"
SOURCE = PROJECT / "Playground/Scratch.lean"
SETUP_CACHE_LAKE = PROJECT / ".lake/toolchains/lean4/build/release/stage2/bin/lake"
HEADER_RE = re.compile(r"^\s*(module|prelude|(public\s+|meta\s+|private\s+)*import)\b")
CONFIG_NAMES = ("LEAN_SEARCH_INDEX_CACHE_DIR", "LEAN_TACTIC_INDEX_DIR")


def set_clone_runtime_env(env: dict[str, str]) -> None:
    env["LEAN_PATH"] = clone_lean_path(env)
    env["LEAN_SYSROOT"] = str(PREFIX)
    for name in ("DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"):
        old = [p for p in env.get(name, "").split(os.pathsep) if p]
        old = [p for p in old if not p.startswith(str(PROJECT / ".lake/toolchains/lean4"))
               and not p.startswith(str(PREFIX))]
        env[name] = os.pathsep.join([str(PREFIX / "lib/lean"), str(PREFIX / "lib"), *old])


def digest(path: Path, quick: bool = False) -> str:
    h = hashlib.sha256()
    size = path.stat().st_size
    with path.open("rb") as f:
        if quick:
            h.update(str(size).encode())
            h.update(f.read(65536))
            if size > 65536:
                f.seek(max(0, size - 65536)); h.update(f.read(65536))
        else:
            for chunk in iter(lambda: f.read(1 << 20), b""):
                h.update(chunk)
    return h.hexdigest()


def stat_id(path: Path) -> list[int]:
    st = path.stat()
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]


def dependency_files() -> list[Path]:
    deps = json.loads(Path(str(SNAPSHOT) + ".deps").read_text())
    keys = ("olean", "oleanServer", "oleanPrivate", "irSig", "ir")
    return sorted({Path(p).resolve() for art in deps for key in keys if (p := art.get(key))})


def header_text(path: Path) -> str:
    lines = path.read_text().split("\n")
    end = 0
    for i, line in enumerate(lines):
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        if HEADER_RE.match(line):
            end = i + 1
            continue
        break
    return "\n".join(lines[:end]).rstrip()


def clone_lean_path(env: dict[str, str]) -> str:
    paths = env.get("LEAN_PATH", "").split(os.pathsep)
    core = str(PREFIX / "lib/lean")
    paths = [p for p in paths if p and not p.endswith("/stage2/lib/lean")]
    return os.pathsep.join(paths + [core])


def linked_runtime_files() -> list[Path]:
    out = subprocess.check_output(["otool", "-L", str(LEAN)], text=True)
    files = [LEAN.resolve()]
    for line in out.splitlines()[1:]:
        name = line.strip().split(" ", 1)[0]
        if name.startswith("@rpath/"):
            candidate = PREFIX / "lib/lean" / name.removeprefix("@rpath/")
            if candidate.exists(): files.append(candidate.resolve())
    return sorted(set(files))


def direct_trace(env: dict[str, str], module: str = "Mathlib") -> tuple[str, str]:
    rel = module.replace(".", "/") + ".trace"
    for directory in clone_lean_path(env).split(os.pathsep):
        path = Path(directory) / rel
        if path.exists():
            return str(path.resolve()), json.loads(path.read_text()).get("depHash")
    raise FileNotFoundError(rel)


def current_identity(env: dict[str, str], include_mapped: bool = True) -> dict:
    trace_path, trace_hash = direct_trace(env)
    project_files = [PROJECT / n for n in ("lakefile.toml", "lake-manifest.json")]
    result = {
        "schema": 1,
        "project": str(PROJECT.resolve()),
        "snapshot_stat": stat_id(SNAPSHOT),
        "snapshot_digest": digest(SNAPSHOT, quick=True),
        "deps_stat": stat_id(Path(str(SNAPSHOT) + ".deps")),
        "deps_digest": digest(Path(str(SNAPSHOT) + ".deps"), quick=True),
        "setup_digest": digest(SETUP),
        "setup_cache_launcher": digest(SETUP_CACHE_LAKE),
        "runtime": {str(p): [stat_id(p), digest(p, quick=True)] for p in linked_runtime_files()},
        "config": {name: env.get(name) for name in CONFIG_NAMES},
        "runtime_env_prefix": {name: env.get(name, "").split(os.pathsep)[:2]
                               for name in ("DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH")},
        "lean_path": clone_lean_path(env),
        "direct_import_trace": [trace_path, trace_hash],
        "project_files": {str(p): digest(p) for p in project_files if p.exists()},
        "toolchain_allowed": ["lean-v4.33.1-optimized", "lean-v4.33.1-server-snapshot"],
        "canonical_header": header_text(SOURCE),
    }
    if include_mapped:
        # Exact mapped region files, derived from the snapshot sidecar rather than a project scan.
        result["mapped_dependencies"] = {str(p): stat_id(p) for p in dependency_files()}
    return result


def validate(env: dict[str, str]) -> tuple[bool, str]:
    try:
        saved = json.loads(MANIFEST.read_text())
        # Avoid rebuilding the 52k-entry dependency dictionary. Check fixed identity first, then
        # stat each exact dependency path recorded from the sidecar.
        mapped = saved.pop("mapped_dependencies")
        now = current_identity(env, include_mapped=False)
        if now != saved:
            differing = [k for k in now if now.get(k) != saved.get(k)]
            return False, "manifest mismatch: " + ", ".join(differing)
        for name, expected in mapped.items():
            if stat_id(Path(name)) != expected:
                return False, f"mapped dependency changed: {name}"
        if Path.cwd().resolve() != PROJECT.resolve():
            return False, f"project cwd differs: {Path.cwd()}"
        return True, "validated binary, runtime, setup, config, project, and Mathlib trace"
    except Exception as e:
        return False, f"validation error: {e}"


def serve(argv: list[str]) -> None:
    env = dict(os.environ)
    set_clone_runtime_env(env)
    # Preserve the playground's already-installed setup-file cache. Its eligibility gate and
    # cache key see the cloned sysroot/LEAN_PATH, so this creates a separate safe entry.
    env["LAKE"] = str(SETUP_CACHE_LAKE)
    # Loading an eagerly saved snapshot is compatible with the normal lazy runtime.  Keeping this
    # unset preserves ordinary miss performance and is part of this experiment's tested setup.
    env.pop("LEAN_LAZY_PARTS", None)
    is_server = len(argv) >= 1 and argv[0] == "--server"
    if is_server:
        # Watchdog inherits this and invokes us anew for every worker. This makes dependency
        # validation per-worker instead of a one-time server-start check.
        env["LEAN_WORKER_PATH"] = str(Path(__file__).resolve())
    scratch_uri = SOURCE.resolve().as_uri()
    worker_uri = next((a.split("=", 1)[1] for a in argv if a.startswith("--worker=")), None)
    if worker_uri is None and "--worker" in argv:
        # Watchdog appends its server arguments and then the document URI.
        worker_uri = argv[-1] if argv else None
    eligible = worker_uri == scratch_uri and Path.cwd().resolve() == PROJECT.resolve()
    if eligible:
        # The watchdog may normalize LEAN_PATH while starting workers. Restore the exact path used
        # to build and validate the project-specific snapshot before setup-file or snapshot load.
        try: env["LEAN_PATH"] = json.loads(MANIFEST.read_text())["lean_path"]
        except Exception: pass
    ok, reason = validate(env) if eligible else (False, "worker is not the canonical Scratch document")
    if ok:
        env["LEAN_SERVER_SNAPSHOT"] = str(SNAPSHOT)
        print(f"LEAN_SERVER_SNAPSHOT launcher hit: {reason}", file=sys.stderr, flush=True)
    else:
        env.pop("LEAN_SERVER_SNAPSHOT", None)
        if worker_uri is not None:
            print(f"LEAN_SERVER_SNAPSHOT launcher fallback: {reason}", file=sys.stderr, flush=True)
    os.execve(LEAN, [str(LEAN), *argv], env)


def main() -> None:
    if sys.argv[1:] == ["build-manifest"]:
        env = dict(os.environ)
        set_clone_runtime_env(env)
        MANIFEST.write_text(json.dumps(current_identity(env), indent=2, sort_keys=True) + "\n")
        print(MANIFEST)
        return
    if sys.argv[1:] in (["check"], ["validate-worker"]):
        env = dict(os.environ); set_clone_runtime_env(env)
        ok, reason = validate(env); print(json.dumps({"ok": ok, "reason": reason}))
        raise SystemExit(0 if ok else 1)
    serve(sys.argv[1:])


if __name__ == "__main__":
    main()
