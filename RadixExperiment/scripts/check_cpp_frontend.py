#!/usr/bin/env python3
"""Compare the exact source snippets in Lean's frontend tests with native C++.

The single-line `#guard outputOf "..." == some "..."` assertions in
Radix/Tests/CppCorrespondence.lean are the authoritative snippets and expected
outputs. Their string escapes are the JSON-compatible subset of Lean strings.
No second handwritten source or expected-output list is maintained here.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / "Radix/Tests/CppCorrespondence.lean"


def cases_from_lean(path=TESTS):
    decoder = json.JSONDecoder()
    cases = []
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        marker = "#guard outputOf "
        if not line.startswith(marker):
            continue
        source, consumed = decoder.raw_decode(line[len(marker):])
        remainder = line[len(marker) + consumed:].strip()
        assert remainder.startswith("== some "), (path, line_number)
        expected = decoder.decode(remainder[len("== some "):])
        assert isinstance(source, str) and isinstance(expected, str)
        cases.append((line_number, source, expected.encode("utf-8")))
    assert cases, f"no native correspondence assertions found in {path}"
    return cases


def check(build_proofs=True):
    if build_proofs:
        subprocess.run(["lake", "build", "Radix.Tests.CppCorrespondence"],
                       cwd=ROOT, check=True)
    compiler = shlex.split(os.environ.get("CXX", "clang++"))
    # Deliberately unparenthesized precedence cases can warn. Keep warnings
    # enabled; the benchmark programs are separately compiled with -Werror.
    flags = ["-std=c++20", "-O2", "-Wall", "-Wextra"]
    prelude = (ROOT / "runtime/radix_io.hpp").read_bytes()
    cases = cases_from_lean()
    warnings = 0
    with tempfile.TemporaryDirectory(prefix="radix-cpp-frontend-") as directory:
        directory = Path(directory)
        for line_number, source, expected in cases:
            source_path = directory / "case.cpp"
            binary = directory / "case"
            source_path.write_bytes(prelude + b"\n" + source.encode("utf-8") +
                                    b"\nint main() { solve(); return 0; }\n")
            compiled = subprocess.run(compiler + flags + [str(source_path), "-o", str(binary)],
                                      capture_output=True, text=True)
            if compiled.returncode:
                raise AssertionError(f"{TESTS}:{line_number}: native compilation failed\n"
                                     f"{compiled.stderr}")
            warnings += compiled.stderr.count("warning:")
            ran = subprocess.run([str(binary)], capture_output=True, timeout=5)
            assert ran.returncode == 0 and ran.stdout == expected, (
                f"{TESTS}:{line_number}", ran.returncode, ran.stdout, expected, ran.stderr)
    return {
        "kind": "local C++/Lean frontend regression checks, not a compiler proof",
        "cases": len(cases),
        "proof_build_run": build_proofs,
        "compiler": subprocess.check_output(compiler + ["--version"], text=True).strip(),
        "flags": flags,
        "warnings": warnings,
        "test_sha256": hashlib.sha256(TESTS.read_bytes()).hexdigest(),
        "prelude_sha256": hashlib.sha256(prelude).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-only", action="store_true", help="skip the Lean test build")
    args = parser.parse_args()
    print(json.dumps(check(build_proofs=not args.native_only), indent=2))


if __name__ == "__main__":
    main()
