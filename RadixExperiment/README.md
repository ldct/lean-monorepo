# RadixExperiment

Radix is an imperative language with Lean big-step semantics, a fuel-limited
interpreter, and five proved optimizer passes. This repository also contains a
Verso slide deck about its development.

See [RSTMT_DESIGN.md](RSTMT_DESIGN.md) for the implemented language design,
execution model, proof architecture, and trust boundaries.

The AtCoder work adds a checked C++ subset and standalone ABC177 C sources.
The complete ABC177 C theorem is
`Radix.Benchmarks.ABC177C.refinement : Refines reference optimized`.
It relates the programs parsed from the exact standalone source files, including
validation, allocation, computation, and output. The optimized running-sum loop
replaces the reference's quadratic pair enumeration.

## Build and reproduce

Use the pinned Lean toolchain (`lean-toolchain`).

```sh
lake build Radix
lake build
python3 scripts/check_abc177c.py --report benchmarks/abc177c/local-results.json
```

The script builds both Lean targets, compiles the exact standalone sources with
`clang++ -std=c++20 -O2 -Wall -Wextra -Werror`, checks official samples,
200 deterministic randomized instances, boundary and malformed inputs, and the
shared runtime's scanner and rejection behavior. It checks a maximum-size
optimized run against an independent Python exact-integer oracle and times the
reference with a two-second timeout. Set `CXX` to select another compiler;
`--native-only` skips the proof builds. Reports record platform, compiler,
source/prelude SHA-256 identities, and whether proof builds ran. Measurements
are local evidence, not AtCoder verdicts.

The submitted artifact is [benchmarks/abc177c/optimized.cpp](benchmarks/abc177c/optimized.cpp).
Both it and [the quadratic reference](benchmarks/abc177c/reference.cpp) embed
[runtime/radix_io.hpp](runtime/radix_io.hpp) verbatim and need no external header.
They retain identical validation and allocate one input array.
The samples and constraints are from
[ABC177 C — Sum of product of pairs](https://atcoder.jp/contests/abc177/tasks/abc177_c?lang=en).

## Execution contract

`Radix.Proofs.Refinement` defines the common, fuel-free interface:

```lean
def Refines (reference optimized : Program) : Prop :=
  ∀ input output,
    RunsSuccessfully reference input output →
    RunsSuccessfully optimized input output
```

Successful execution starts with the program's own function table, empty locals
and heap, the supplied input bytes, and empty output. It must terminate normally
or return normally, with the complete final output. Rejection, runtime faults,
and divergence impose no obligation on the optimized program. The reference's
executable validation determines its domain; there is no problem-specific
predicate in this interface. Generic reflexivity, transitivity, and output
uniqueness are proved.

`StmtResult` distinguishes normal completion, return, and rejection.
`InterpError` distinguishes explicit rejection, runtime faults, and fuel
exhaustion. Streams are shared across calls. Output produced before rejection
remains an observable prefix, but does not constitute a successful answer.
Logical `&&` and `||` short-circuit even when the skipped operand would fault.

Arrays are ordinary aliases to persistent heap allocations. There is no
linearity checker or deallocation operation. `BigStep.heap_persistent` proves
that existing allocations retain their lengths and remain present across
execution, assuming the initial bump allocator is well formed. Standard initial
states satisfy that condition. Reads and writes still check array bounds.

The fixed scanner accepts ASCII decimal unsigned tokens up to `2^64-1`, with
optional leading zeros, and whitespace bytes 9–13 and 32. It rejects signs,
overflow, missing or malformed tokens. Reads consume the first trailing
whitespace byte. `expect_eof()` accepts only remaining whitespace; the unsigned
printer uses canonical decimal formatting. Literal writes control separators.

## Checked source and trust boundaries

[Radix/Frontend/Cpp.lean](Radix/Frontend/Cpp.lean) accepts the exact known prelude,
`void solve()` in the supported subset, and the fixed
`int main() { solve(); return 0; }` wrapper. Its dedicated grammar checks
C++ precedence, initialized declarations, exact types, lexical scopes, array
aliases, and reserved helper names. Local declarations lower to unique internal
IDs and execute each time control reaches them. Unsupported C++ syntax is
rejected. Source integer literals require `ULL`; octal literals are excluded.

[Radix/Benchmarks/ABC177C.lean](Radix/Benchmarks/ABC177C.lean) embeds the actual
standalone files and exposes parsing equations for them. Lake tracks both
source files and the runtime header as byte-sensitive input dependencies, so
changes invalidate proof builds. Source locals use `[a-z][a-z0-9]*`, excluding
reserved keywords and macro names, to avoid C++ header macro collisions.
There are no alternate algorithm bodies
selected by preprocessing. Editing the prelude requires updating both embedded
copies; a mismatch fails parsing and native checks.

The parser's agreement with C++ and the shared native runtime contract are
trusted. Concrete parsing certificates use Lean's native decision procedure,
which introduces per-certificate `native_decide` axioms trusting compiled Lean
evaluation. This is confined to source parsing. The whole-program refinement
proof itself uses only `propext`, `Classical.choice`, and `Quot.sound`.
The reproducibility command prints the axiom dependencies even on cached builds. These boundaries must not
be mistaken for a verified C++ compiler or an independent target simulation.
Native execution additionally relies on the compiler, standard library,
allocator, OS, and hardware, with adequate resources and working byte transport.
Logical allocation persistence does not prove a native memory limit.

## Proofs and layout

- `Radix/AST.lean`, `State.lean`, `Heap.lean`, `Eval/`: language and execution.
- `Radix/Proofs/`: determinism, interpreter correctness, expression type
  preservation, allocation persistence, refinement, and total-correctness rules.
- `Radix/Opt/`: constant folding, dead-code elimination, copy propagation,
  constant propagation, and inlining, with preservation proofs.
- `Radix/Frontend/`: authoritative C++ source parsing and checking.
- `Radix/Benchmarks/`: source artifacts, pair-sum algebra, and machine proof work.
- `Radix/Tests/`: executable language and optimizer regressions.
- `Slides.lean`, `Main.lean`, `static/`: the presentation; run
  `.lake/build/bin/radix-slides` to generate `_out/`.

Internal `[RStmt| ...]` quotations remain useful for tests and slide examples.
They are not the source of the benchmark parsing evidence. Expression type
preservation is not a general progress theorem: well-typed expressions can
still fault on division by zero or invalid array indices.

## License

Apache-2.0

## Proposal milestone status

All seven required milestones are implemented:

| Milestone | Result |
| --- | --- |
| 1. Remove linearity and deallocation | Persistent allocations, length-preservation proof, aliasing tests |
| 2. Execution and refinement | Distinct outcomes, short-circuiting, determinism, interpreter correspondence, generic refinement |
| 3. Shared I/O | Logical byte streams, checked scanner/printer, standalone native prelude, contract regressions |
| 4. C++ frontend | Dedicated typed grammar, lexical name resolution, exact source/prelude parsing certificates |
| 5. Executable ABC177 C | Validating quadratic reference and linear submission, native and interpreter sample checks |
| 6. Whole-program proof | `ABC177CRefinement.refinement`, including input validation, finite loops, bounds, and full output |
| 7. Packaging and validation | Both Lake builds, axiom audit, native differential/oracle checks, maximum-size timing and source identities |

`python3 scripts/check_cpp_frontend.py` separately runs the frontend's Lean and
native correspondence regressions. The main reproducibility command also runs
the native side, using snippets extracted directly from the Lean test file.
These tests supplement the shared parser trust boundary; they are not a C++
semantics proof. No AtCoder submission or verdict is claimed.
