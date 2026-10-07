#!/usr/bin/env python3
"""Probe a minimal upstream proof-source closure against the unchanged Lean pin.

This script is for CI diagnostics only. It does not commit files, alter the
Mathlib checkout, or treat upstream claims as axioms. Each copied source is
compiled with Lean 4.32.0 and selected capstones receive a transitive audit.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

UPSTREAM = "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git"
REVISION = "a5154676af9aa3095150ee410cdda80555aa0642"
ROOTS = [
    "PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard",
    "PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation",
]
IMPORT = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_'.]+)", re.M)
CAPSTONES = [
    "riemannXi_entireOfOrderAtMost_one",
    "summable_riemannXi_divisorZeroIndex₀_norm_inv_sq",
    "riemannXi_hadamard_factorization_no_monomial",
    "exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum",
]


def main() -> int:
    package = Path(__file__).resolve().parents[1]
    report = package / "hadamard-probe-report.md"
    notes = ["# Pinned Hadamard compatibility probe", "", f"Upstream `{REVISION}`.",
             "The project toolchain and Mathlib pin are not changed.", ""]
    print("\n".join(notes), flush=True)
    with tempfile.TemporaryDirectory(prefix="lagarias-upstream-") as tmp:
        upstream = Path(tmp)
        subprocess.run(["git", "init", "-q", str(upstream)], check=True)
        subprocess.run(["git", "-C", str(upstream), "fetch", "--depth=1", UPSTREAM, REVISION], check=True)
        subprocess.run(["git", "-C", str(upstream), "checkout", "-q", "FETCH_HEAD"], check=True)
        order: list[str] = []
        sources: dict[str, str] = {}
        active: set[str] = set()
        external: set[str] = set()

        def visit(module: str) -> None:
            if module in sources:
                return
            if module in active:
                raise RuntimeError(f"Cyclic import at {module}")
            active.add(module)
            source = upstream.joinpath(*module.split(".")).with_suffix(".lean")
            text = source.read_text(encoding="utf-8")
            for imported in IMPORT.findall(text):
                if imported.startswith("PrimeNumberTheoremAnd."):
                    visit(imported)
                elif not imported.startswith(("Mathlib", "Lean", "Init", "Batteries", "Std")):
                    external.add(imported)
            active.remove(module)
            sources[module] = text
            order.append(module)

        for root in ROOTS:
            visit(root)
        notes.append(f"Minimal source closure: {len(order)} modules.")
        notes.append(f"Additional import roots: {sorted(external)}")
        manifest = {module: hashlib.sha256(text.encode()).hexdigest() for module, text in sources.items()}
        (package / "hadamard-probe-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        for module in order:
            text = sources[module]
            if re.search(r"\b(?:sorry|admit|axiom)\b", text):
                notes.append(f"Source-token review needed: `{module}` (may include comments).")
            target = package.joinpath(*module.split(".")).with_suffix(".lean")
            if target.exists():
                raise RuntimeError(f"Refusing to overwrite {target}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        print("\n".join(notes), flush=True)
        for module in order:
            source = Path(*module.split(".")).with_suffix(".lean")
            output = package / ".lake/build/lib/lean" / source.with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            command = ["lake", "env", "lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                       "-o", str(output), str(source)]
            print(f"Compiling {module}", flush=True)
            try:
                result = subprocess.run(command, cwd=package, text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=300)
            except subprocess.TimeoutExpired as exc:
                notes.extend([f"## Timed out: `{module}`", "```text", str(exc.stdout)[-16000:], "```"])
                report.write_text("\n".join(notes) + "\n")
                return 1
            if result.returncode:
                notes.extend([f"## Compilation failed: `{module}`", "```text", result.stdout[-20000:], "```"])
                report.write_text("\n".join(notes) + "\n")
                print(result.stdout, flush=True)
                return result.returncode
            notes.append(f"Compiled `{module}`.")
        audit = "\n".join("import " + module for module in ROOTS)
        audit += "\nimport Lean.Util.CollectAxioms\n\nopen Lean Elab Command in\nrun_cmd do\n"
        audit += "  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]\n"
        audit += "  let names := #[" + ", ".join("``" + name for name in CAPSTONES) + "]\n"
        audit += "  for name in names do\n"
        audit += "    let axioms ← Lean.collectAxioms name\n"
        audit += "    unless (axioms.filter fun n => !allowed.contains n).isEmpty do\n"
        audit += '      throwError "Forbidden dependency: {name}: {axioms}"\n'
        audit += '    logInfo m!"AUDITED {name}: {axioms}"\n'
        audit_path = package / "HadamardProbeAudit.lean"
        audit_path.write_text(audit, encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(audit_path)], cwd=package, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        notes.extend(["## Capstone audit", "```text", result.stdout, "```"])
        report.write_text("\n".join(notes) + "\n")
        print(result.stdout, flush=True)
        return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
