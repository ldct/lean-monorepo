#!/usr/bin/env python3
"""Build proofs and test the exact standalone sources; results are local, not verdicts."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import shlex
import subprocess
import tempfile
import time

from check_cpp_frontend import check as check_frontend

ROOT = Path(__file__).resolve().parents[1]
MOD = 1_000_000_007


def run(binary, data, timeout=5):
    return subprocess.run([str(binary)], input=data, capture_output=True, timeout=timeout)


def encode(values):
    return (str(len(values)) + "\n" + " ".join(map(str, values)) + "\n").encode()


def oracle(values):
    # Exact integers and the square identity, independent of either source loop.
    return ((sum(values) ** 2 - sum(x * x for x in values)) // 2) % MOD


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-only", action="store_true", help="skip Lean builds")
    parser.add_argument("--report", type=Path, help="write reproducibility report as JSON")
    parser.add_argument("--reference-timeout", type=float, default=2.0)
    args = parser.parse_args()
    if not args.native_only:
        subprocess.run(["lake", "build", "Radix"], cwd=ROOT, check=True)
        subprocess.run(["lake", "build"], cwd=ROOT, check=True)
        audit = subprocess.check_output(
            ["lake", "env", "lean", "scripts/check_axioms.lean"], cwd=ROOT, text=True)
        print(audit, end="")
        assert "sorryAx" not in audit, "unfinished proof in axiom dependencies"
    compiler = shlex.split(os.environ.get("CXX", "clang++"))
    flags = ["-std=c++20", "-O2", "-Wall", "-Wextra", "-Werror"]
    prelude = (ROOT / "runtime/radix_io.hpp").read_bytes()
    sources = {name: ROOT / f"benchmarks/abc177c/{name}.cpp"
               for name in ("reference", "optimized")}
    for source in sources.values():
        assert source.read_bytes().startswith(prelude + b"\nvoid solve() {\n"), source
        assert source.read_bytes().endswith(b"\nint main() { solve(); return 0; }\n"), source
    report = {
        "kind": "local measurements, not AtCoder verdicts",
        "platform": platform.platform(),
        "compiler": subprocess.check_output(compiler + ["--version"], text=True).strip(),
        "flags": flags,
        "proof_builds_run": not args.native_only,
        "frontend_correspondence": check_frontend(build_proofs=False),
        "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in [ROOT / "runtime/radix_io.hpp", *sources.values()]},
    }
    with tempfile.TemporaryDirectory(prefix="radix-abc177c-") as directory:
        binaries = {name: Path(directory) / name for name in sources}
        for name, source in sources.items():
            subprocess.run(compiler + flags + [str(source), "-o", str(binaries[name])], check=True)
        rng = random.Random(177)
        cases = [[1, 2, 3], [141421356, 17320508, 22360679, 244949],
                 [0, 0], [10**9, 10**9], [0, 10**9], [10**9] * 100]
        assert oracle(cases[0]) == 11 and oracle(cases[1]) == 437235829
        cases += [[rng.randrange(10**9 + 1) for _ in range(rng.randrange(2, 60))]
                  for _ in range(200)]
        for values in cases:
            expected = f"{oracle(values)}\n".encode()
            for binary in binaries.values():
                result = run(binary, encode(values))
                assert result.returncode == 0 and result.stdout == expected, (values, result)
        invalid = [b"", b"1\n0", b"200001\n", b"2\n0", b"2\n0 1000000001",
                   b"2\n0 0 x", b"2\n0 0 0", b"+2\n0 0", b"-2\n0 0",
                   b"2\n0 +0", b"2\n0 -0", b"2\n0 0x", b"2\n0 0\x00",
                   b"18446744073709551616", b"2\n0 18446744073709551615"]
        for data in invalid:
            for binary in binaries.values():
                assert run(binary, data).returncode != 0, data
        for data in [b"2 0 0", b"\t\n\v\f\r 0002\t0000\v00\f\r\n "]:
            for binary in binaries.values():
                result = run(binary, data)
                assert result.returncode == 0 and result.stdout == b"0\n"
        # Probe the shared runtime independently of benchmark domain validation.
        probe = Path(directory) / "runtime.cpp"
        probe.write_bytes(prelude + b'\nint main() { u64 x = 0ULL; read_u64(x); '
                          b'expect_eof(); write_u64(x); write_text("\\n"); }\n')
        probe_bin = Path(directory) / "runtime"
        subprocess.run(compiler + flags + [str(probe), "-o", str(probe_bin)], check=True)
        for data, expected in [(b"0", b"0\n"), (b"00042\t", b"42\n"),
                               (b"18446744073709551615", b"18446744073709551615\n")]:
            result = run(probe_bin, data)
            assert result.returncode == 0 and result.stdout == expected
        for data in [b"", b" ", b"+1", b"-1", b"1x", b"1 2", b"18446744073709551616"]:
            assert run(probe_bin, data).returncode != 0
        probe.write_bytes(prelude + b'\nint main() { write_u64(123ULL); write_text("\\n"); reject(); }\n')
        subprocess.run(compiler + flags + [str(probe), "-o", str(probe_bin)], check=True)
        rejected = run(probe_bin, b"")
        assert rejected.returncode != 0 and rejected.stdout == b"123\n"
        values = [rng.randrange(10**9 + 1) for _ in range(200000)]
        data, expected = encode(values), f"{oracle(values)}\n".encode()
        start = time.perf_counter()
        result = run(binaries["optimized"], data)
        report["optimized_max_seconds"] = time.perf_counter() - start
        assert result.returncode == 0 and result.stdout == expected
        start = time.perf_counter()
        try:
            result = run(binaries["reference"], data, timeout=args.reference_timeout)
            report["reference_max_seconds"] = time.perf_counter() - start
            assert result.returncode == 0 and result.stdout == expected
        except subprocess.TimeoutExpired:
            report["reference_max_timeout_seconds"] = args.reference_timeout
        report["small_valid_cases_per_program"] = len(cases) + 2
        report["invalid_cases_per_program"] = len(invalid)
        report["runtime_contract_probes"] = "passed"
    output = json.dumps(report, indent=2) + "\n"
    print(output, end="")
    if args.report:
        args.report.write_text(output)


if __name__ == "__main__":
    main()
