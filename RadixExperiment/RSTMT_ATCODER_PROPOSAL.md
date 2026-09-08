**Proposal: directly submittable RStmt programs for AtCoder benchmarks**

Prepared 2026-09-08. This is a design proposal, supported by local experiments. It does not implement the proposed language changes or establish a verified C++ backend.

This document is the implementation handoff. Its required deliverable is the revised language infrastructure and one completed benchmark, ABC177 C. The final milestone list defines completion. Examples of other problems explain design choices or possible future work; they are not additional implementation tasks. The design and the checked algebra below are self-contained and do not depend on the preceding conversation or temporary experiment files.

Make RStmt's supported source language a small, precisely specified subset of C++, with a fixed shared I/O prelude. Use one theorem template for every benchmark: the optimized program preserves every successful complete execution of the reference program. Let the reference establish its own input domain through executable validation and explicit rejection. Start with ordinary batch problems whose answers are unique integers or strings.

The deliverable for each benchmark should be a reference source file, an optimized source file, and a proof relating the programs parsed from those exact files. Both source files should compile as C++ with the shared prelude embedded. The optimized file is the submission; there is no separately handwritten translation of the verified algorithm.

**The reference is the executable specification, including its domain.** Define the common theorem schematically as follows:

```lean
def Refines (reference optimized : Program) : Prop :=
  ∀ (input output : ByteArray),
    RunsSuccessfully reference input output →
    RunsSuccessfully optimized input output
```

`RunsSuccessfully` means a complete, finite execution from the standard initial state, ending successfully with exactly `output` on stdout. It does not mean that some finite prefix printed those bytes. Initialization uses the program's own function table, empty local state and heap, the given input, and empty output.

This theorem has no problem-specific graph type, decoding predicate, or validity hypothesis. A benchmark author can instantiate it mechanically with two programs. Understanding the problem is needed to write and review the reference; it is not needed a second time to choose the theorem's preconditions. Proving a substantial algorithmic optimization will still require invariants and mathematical reasoning.

For a problem that promises an acyclic graph, the reference can execute a cycle check and call `reject()` when a cycle exists. There are no successful reference executions on cyclic graphs, so the refinement theorem imposes no requirements there. If the reference instead computes an answer on cyclic graphs, that extra behavior is part of its specification and must be preserved. There is no mechanism that infers exclusions from the English problem statement.

The reference can validate sizes, ranges, distinctness, graph structure, and complete input consumption using ordinary statements. Such validation may be slow. It should precede accesses or allocations that depend on the property being checked. Use explicit rejection for intentional exclusions; do not use division by zero or undefined C++ behavior as a substitute for validation.

This is directional refinement, not unrestricted equivalence. Its intended obligations are:

| Reference execution | Required optimized behavior |
| --- | --- |
| Finishes successfully with output `o` | Must finish successfully with exactly `o` |
| Explicitly rejects | Unconstrained by this theorem |
| Encounters a runtime fault | Unconstrained by this theorem; ordinarily a reference bug to investigate |
| Diverges | Unconstrained by this theorem |

The reference can take more time than AtCoder permits and still have a successful mathematical execution. The optimized program cannot replace such an execution with rejection or divergence. The relational semantics and the refinement theorem have no fuel parameter and impose no equal-cost requirement.

The theorem is deliberately relative to a trusted reference. A reference that rejects every input makes it vacuous. A reference that accepts and prints a wrong answer specifies that wrong answer. Samples, independent small-instance checks, and review of the reference are therefore part of benchmark curation. They do not prove coverage of every official input. A separate formalization of the problem could prove that coverage, but requiring it would defeat the desired mechanical theorem interface.

**Rejection must be a distinct control-flow outcome.** Add `Stmt.reject` and an explicit rejected statement result. Propagate rejection out of sequences, loops, lexical blocks, function calls, and the internal inlining construct. A callee's rejection terminates the whole program; it is not an ordinary function return that the caller can ignore.

The execution interface should distinguish successful completion, explicit rejection, and runtime fault. Keep interpreter fuel exhaustion as a separate testing outcome. Runtime faults include invalid accesses and arithmetic operations outside the supported semantics. The initial relational semantics may continue to describe successful runs with big-step rules, while adding rejection rules and retaining fault diagnostics in the interpreter; success must not be inferred merely from the absence of an explicit rejection rule.

Use a fixed C++ helper such as `[[noreturn]] void reject()` implemented by `std::exit(EXIT_FAILURE)`. Do not use an assertion macro whose checks can disappear under `NDEBUG`, or an optimizer assumption that gives undefined behavior when false. C++ specifies `EXIT_FAILURE` as unsuccessful termination. Its exit machinery may flush already-buffered output, so rejection must be identified by the outcome, not by empty stdout. [C++ termination facilities](https://eel.is/c++draft/support.start.term)

For example, this program has no successful execution:

```cpp
write_u64(123ULL);
write_text("\n");
reject();
```

Its emitted bytes remain part of the observed prefix on a rejected execution. They do not become an accepted answer. Nothing requires transactional output buffering or undoing physical writes. On successful executions, compare the entire final output. Batch semantics can omit read/write timing and flushing; interactive protocols are outside the initial scope.

Use the fixed wrapper `int main() { solve(); return 0; }`, with a `void solve()` body in the supported subset. Successful fallthrough or a normal `return;` from `solve` accepts; `reject()` does not. Arbitrary exit-status expressions in a user-written `main` are outside the first frontend. The current `Program.run` discards return values, so merely spelling rejection as `return 1;` is insufficient.

**I/O belongs in RStmt, with a reusable runtime boundary.** Extend the logical machine state with immutable input bytes, a natural-number cursor, and an output byte sequence. The cursor and output are shared across function calls, just like the heap. Frames do not get independent copies of the streams. Expressions remain pure; I/O occurs only in statements.

Start with these surface operations and corresponding AST forms:

| C++ source | Logical effect |
| --- | --- |
| `read_u64(x);` | Consume an unsigned decimal token and assign its value to a declared scalar |
| `write_u64(e);` | Evaluate the pure expression and append its decimal representation |
| `write_text("literal");` | Append the specified literal bytes |
| `expect_eof();` | Consume remaining whitespace and reject if anything else remains |
| `reject();` | End the execution with explicit rejection |

An array read can initially be written as `read_u64(x); a[i] = x;`, keeping the input destination rule simple. Output strings can initially be literals, so numeric benchmarks do not require the existing general string type. Later add signed tokens, byte strings, and character operations as benchmarks need them.

Specify the scanner precisely, independently of the problem:

- Whitespace bytes are ASCII 9 through 13 and ASCII 32.
- An unsigned token has one or more digits `0` through `9`, optionally with leading zeros, and represents a value at most `2^64 - 1`.
- Signs and non-digit bytes inside a token reject. Missing tokens and overflow reject. A successful read consumes the first trailing whitespace byte when present; the next call skips any remaining whitespace. Ending immediately after the final digit is allowed.
- EOF is distinct from any byte value. `expect_eof()` accepts only whitespace followed by EOF.
- Unsigned output is canonical decimal with no leading zeros except for zero itself. Literal writes control spaces and newlines explicitly.

These are choices for the benchmark language's accepted input domain. For example, a leading plus sign is rejected even if another parser would accept it. A problem whose official encoding needs a different token form must use an appropriate additional primitive. There is no implicit promise that arbitrary bytes have already been decoded into valid integers.

Prefer these small helpers over treating unrestricted `std::cin` and `std::cout` as primitive statements. Standard numeric stream extraction and formatting depend on stream configuration and locale. A fixed helper with explicit byte rules gives a simpler shared contract, particularly on malformed inputs. [C++ numeric extraction](https://eel.is/c++draft/istream.formatted.arithmetic), [numeric insertion](https://eel.is/c++draft/ostream.inserters.arithmetic)

Initially the scanner/printer implementation and its connection to these rules are trusted once for all benchmarks. All problem-specific parsing loops, validations, array construction, and output decisions are within RStmt and the refinement proof. This is a shared I/O adapter, not a fresh unverified parser for each problem.

An optional follow-up can implement and verify the scanner/printer in the supported language over byte-read and byte-write primitives. That reduces the remaining I/O assumption to byte transport and process execution. It is not required for the first handoff deliverable. Whole-input and whole-output buffers are convenient logical representations; the native implementation can stream or buffer in chunks, provided its contract matches. The model need not force every submission to retain all I/O bytes in memory.

**Use C++ as the initial source language.** AtCoder currently lists C++23 with GCC 15.2.0 and also Lean 4.22.0. Lean is therefore a real alternative, but bundling the present interpreter would measure interpreted AST execution, and the repository currently pins Lean 4.29.0-rc1. Native Lean execution would require a separate design connecting the AST to efficient executable code. C++ directly accommodates the present loops, fixed-width arithmetic, mutable arrays, and heap model. [AtCoder language list](https://atcoder.jp/contests/language-test-202505/rules)

Use an ordinary C++ subset that also compiles under C++20. The initial prelude can declare:

```cpp
using u64 = unsigned long long;
static_assert(std::numeric_limits<u64>::digits == 64);
```

Require `ULL` suffixes for unsigned integer literals. This makes both variables and literals have the same C++ type under the prelude and avoids accidentally evaluating literal-only expressions with `int` arithmetic. Keep the existing modulo-`2^64` unsigned arithmetic. Add signed arithmetic later with explicit range checks in the logical semantics and proofs excluding signed overflow on successful executions. C++ unsigned arithmetic is modular; signed overflow is undefined. [C++ integer types](https://eel.is/c++draft/basic.fundamental)

The source grammar should accept declarations, assignments, array accesses, `if`, `while`, simple returns, restricted calls, allocation, and the fixed I/O helpers. There is no explicit deallocation. For example:

```cpp
u64 n = 0ULL;
read_u64(n);
if (n < 2ULL || n > 200000ULL) { reject(); }
u64* a = new u64[n]();
u64 i = 0ULL;
while (i < n) {
    u64 x = 0ULL;
    read_u64(x);
    a[i] = x;
    i = i + 1ULL;
}
expect_eof();
```

The zero-initializing allocation syntax is intentional. Start with one-dimensional `u64` arrays and flatten tables. Carry lengths explicitly in source. The heap can keep logical lengths for bounds checks, but a raw C++ pointer does not provide `arrLen`. Restrict pointer operations to allocated arrays, copying array references, indexing, and parameter passing. Reject `delete[]`, `delete`, `free`, pointer arithmetic, address casts, and pointer comparisons. Copying an array reference or passing it to a function preserves its identity: aliases refer to the same allocation and observe each other's writes.

Remove the experimental linearity checker from this project. The source language has ordinary typed array references, with no ownership qualifiers, borrowing rules, uniqueness requirements, or requirement to pass `LinearOk`. Remove `Stmt.free` and its evaluation rules from the benchmark language as well. Keep the heap model and explicit failures for invalid array accesses.

Every allocated array remains live for the rest of the execution, even if the allocating block or function returns or the last reference is overwritten. The set of allocated heap addresses only grows; writes change contents without removing allocations. Prove allocation persistence once as a property of the language. Because source references originate from heap allocation and the subset excludes references to stack locals, use-after-free and double-free cases disappear. Benchmark proofs still need array bounds and aliasing reasoning, but do not need a discipline for deciding when storage may be reclaimed.

Raw pointers fit these semantics better than `std::vector`: vector assignment copies elements, whereas address values refer to shared allocations. Raw-pointer locals also have no automatic element destruction on lexical scope exit. Native arrays are left allocated until process termination, with no cleanup loop or hidden deallocation inserted into the verified computation. Allocation identifiers need not equal native addresses; the correspondence relates logical allocations to native allocations.

The tradeoff is cumulative memory usage. Repeated allocation inside a loop retains every array until termination, so optimized submissions should preallocate and reuse workspace where appropriate. Memory limits remain part of empirical benchmark acceptance. Resource exhaustion is an execution-environment limitation, not a theorem that an unbounded logical heap fits into AtCoder memory. Both implementations of the initial benchmark allocate their input array once.

**The frontend needs to enforce C++ meaning, not merely C++ spelling.** Replace the use of Lean's general `term` parser inside RStmt with a dedicated grammar for the supported expressions. Match C++ precedence and associativity; reject unsupported syntax rather than guessing its interpretation. Keep function calls out of pure expressions. A later `x = f(args);` form can lower to a statement-level call with a result destination, without permitting arbitrary nested effectful expressions.

Implement short-circuit `&&` and `||` in expression evaluation. Even pure operands can fail, so eager and short-circuit evaluation differ on `false && (1ULL / 0ULL == 0ULL)`. Revisit expression optimization proofs accordingly. [C++ logical conjunction](https://eel.is/c++draft/expr.log.and)

Require explicit declarations and statement-level typing. Source assignments cannot create variables or change their types. Support lexical scopes through name resolution to unique internal local IDs: a source block determines where a declaration can be referenced, while lowering may retain the existing flat environment inside a call frame. Declarations execute on each entry, including each loop iteration. This avoids introducing a runtime scope stack just to remove inaccessible scalar bindings. It is appropriate only while the subset excludes address-taking of locals, nontrivial destructors, and other observable scope-exit effects. The internal `scope` used by the inliner remains a separate call-frame construct.

The source checker must also enforce initialized use, exact primitive types, supported array operations, function signatures, and the reserved helper names. Initially exclude user macros, conditional compilation, overloads, globals with dynamic initialization, inline assembly, external calls, exceptions/catches, threads, randomness, clocks, and arbitrary pointer operations. These exclusions make a small parser meaningful; RStmt is not a parser for all of C++.

Read the actual submission source into Lean as the authoritative bytes. Permit only the exact known prelude and wrapper outside the parsed subset. For this deliverable, retain the parser's agreement with C++ and the shared runtime implementation as explicit trusted boundaries; verifying them against an independent C++ semantics is optional future work. Bind the theorem artifact to the exact source and prelude versions; any generated submission assembly should be deterministic concatenation with checked sections. There must be no proof-only and submission-only algorithm bodies selected by preprocessor flags.

Source identity reduces translation risk but does not prove native correctness. The initial claim is a Lean proof in the documented subset semantics, conditional on its C++ correspondence and the shared runtime contract. A stronger milestone needs a simulation from checked source executions to an independently defined target semantics. Parsing into the same AST twice does not supply that theorem. Compiler, standard library, allocator, OS, and hardware behavior remain part of native execution assumptions.

**The existing code provides a useful base, with several concrete gaps.** Inspection and local executable probes found:

| Location | Finding and consequence |
| --- | --- |
| [Radix/Syntax.lean](Radix/Syntax.lean) | Expressions currently use Lean `term`; assignments use `:=`; a dedicated C++ subset parser is needed. |
| [Radix/Eval/Expr.lean](Radix/Eval/Expr.lean) | Both binary operands are evaluated before the operator; logical operators are eager. String access uses a raw position while the bounds condition uses `String.length`; defer general strings until their byte/character model is explicit. |
| [Radix/Eval/Stmt.lean](Radix/Eval/Stmt.lean) | Declarations and assignments both call `setVar`; blocks only sequence; allocation ignores its element type and fills with unsigned zeros; function calls discard returned values. |
| [Radix/AST.lean](Radix/AST.lean), [Radix/Heap.lean](Radix/Heap.lean) | Remove explicit deallocation from the benchmark AST and execution paths. Keep allocation, reads, and writes; establish persistence of allocated storage once for the language. |
| [Radix/TypeCheck.lean](Radix/TypeCheck.lean) | The checker covers expressions, not source-level statement well-formedness. |
| [Radix/State.lean](Radix/State.lean) | State has frames, heap, and function table; streams must be added and threaded through every operation. |
| [Radix/Eval/Interp.lean](Radix/Eval/Interp.lean) | Function errors restore the original caller state. This must not erase already-performed I/O. Top-level runners discard return values. Fuel exhaustion currently shares the generic error channel. |
| [Radix/Proofs/InterpCorrectness.lean](Radix/Proofs/InterpCorrectness.lean) | Existing soundness, completeness, and successful-fuel monotonicity are directly relevant; they must be extended for the new constructs. |
| [Radix/Opt/ConstFold.lean](Radix/Opt/ConstFold.lean) and other passes | Existing statement theorems preserve the exact final result/state on successful executions. Keep them as strong local lemmas where useful, and derive output refinement separately. |
| [Radix/Linear.lean](Radix/Linear.lean) | An experiment to remove, together with its dedicated tests and imports. The proposed frontend and benchmark proofs will not depend on `LinearOk`, `OwnershipInv`, or linearity-specific function assumptions. Retain ordinary typing and heap semantics. |

Some state constructors are positional, including allocation in the relational semantics, so simply adding stream fields is insufficient: audit every constructor and frame/heap transformation. A record update should preserve streams unless the statement explicitly changes them.

The final comparison must project to successful output, not equate the entire `PState`. Even the first benchmark's two algorithms have different temporary locals. Later optimizations may change heaps or allocation histories as well. It is also important to project away program-specific function tables.

A whole-program refinement theorem is not automatically a replacement rule for an arbitrary statement context. Two statements that print the same bytes may leave different variables or unread input that a later statement observes. Provide compositional rules with explicit relations on intermediate states. For example, a common parser can be factored out if both algorithm proofs start from the related parsed states; a removed validation routine must not inadvertently change input consumption or data needed by the body.

Maintain directionality when adding optimizations. Removing a failure-producing pure expression can preserve successful behavior even though it does not preserve the exact optional evaluation result. Conversely, removing or moving I/O requires preserving the full accepted output and relevant input state. The existing stronger expression-equality lemmas should not silently change meaning.

**ABC177 C is the sole initial benchmark.** The problem asks for the sum of `A[i] * A[j]` over all `i < j`, modulo `M = 1000000007`, with `2 ≤ N ≤ 200000` and `0 ≤ A[i] ≤ 1000000000`. It has a two-second time limit. [ABC177 C — Sum of product of pairs](https://atcoder.jp/contests/abc177/tasks/abc177_c?lang=en)

Have both implementations read and validate the same array using the same code. Read `N`, reject if it is outside `[2, 200000]`, allocate `N` zero-initialized elements, and read exactly `N` unsigned tokens. Reject any value above `1000000000`; the shared reader already rejects malformed or overflowing tokens. Execute `expect_eof()` after reading the array and before computing the answer. Retain that array in the optimized version too, so the first proof need not also change the parser or heap representation. Retain all validation in both implementations for the first proof.

The reference then literally enumerates the pairs:

```cpp
u64 m = 1000000007ULL;
u64 answer = 0ULL;
u64 j = 0ULL;
while (j < n) {
    u64 i = 0ULL;
    while (i < j) {
        answer = (answer + a[i] * a[j]) % m;
        i = i + 1ULL;
    }
    j = j + 1ULL;
}
```

The optimized computation replaces the inner loop with a running sum:

```cpp
u64 m = 1000000007ULL;
u64 answer = 0ULL;
u64 running = 0ULL;
u64 j = 0ULL;
while (j < n) {
    answer = (answer + running * a[j]) % m;
    running = (running + a[j]) % m;
    j = j + 1ULL;
}
```

Both finish with `write_u64(answer); write_text("\n");`. The key invariant after processing `j` elements is:

```text
running = (sum of a[i] for i < j) mod M
answer  = (sum of a[i] * a[k] for i < k < j) mod M
```

The next element contributes `a[j]` times the sum of preceding elements, by distributivity. Updating `answer` before `running` avoids including a self-pair. The reference's inner-loop invariant is the corresponding partial sum over `i < j`. Both computations can therefore be related to the same pair-sum function using scalar invariants and modular arithmetic. No auxiliary table is mutated and no frequency-counting invariant is needed.

This remains a genuine quadratic-to-linear optimization: at maximum size the reference visits 19999900000 pairs, while the optimized computation makes 200000 iterations. Unsigned arithmetic needs a short, explicit bound argument. Every reduced accumulator is below `M`, each input is at most `10^9`, and even the largest optimized multiply-add is at most `(M - 1) * (10^9 + 1)`, which is below `2^64`. The reference multiply-add also fits. Thus modulo `M` is computed before any unwanted machine wraparound. The loop indices stay within the validated array size.

The mathematical core, including reduction modulo an arbitrary natural-number modulus, was checked in a standalone Lean file using only `Std`. Define `pairs (x :: xs) = x * xs.sum + pairs xs` and strengthen the scan invariant to account for an initial running sum and answer. Induction on `xs`, distributivity, and the standard addition/multiplication modulo lemmas prove the scan returns the pair sum modulo `M`. This checks the central algebra; connecting it to RStmt array reads, loops, successful I/O, and `UInt64` arithmetic is still implementation work.

The following complete Lean proof is retained here so the implementation agent does not need a temporary file. It is an algebraic starting point, not a replacement for the whole-program refinement theorem. `scanMod` applies an extra modulo at its base case; when relating it to the source loop, use the invariant `answer < M` to show that this leaves the stored answer unchanged.

```lean
import Std

namespace PairSumCheck

def pairs : List Nat → Nat
  | [] => 0
  | x :: xs => x * xs.sum + pairs xs

theorem pairs_append_one (xs : List Nat) (x : Nat) :
    pairs (xs ++ [x]) = pairs xs + xs.sum * x := by
  induction xs with
  | nil => simp [pairs]
  | cons y ys ih =>
    simp [pairs, ih, List.sum_append, List.sum_cons,
      Nat.mul_add, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def scanMod (m running answer : Nat) : List Nat → Nat
  | [] => answer % m
  | x :: xs =>
      scanMod m ((running + x) % m) ((answer + running * x) % m) xs

theorem strip_mod (a b c d m : Nat) :
    (a % m + (b % m) * c + d) % m = (a + b * c + d) % m := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem scanMod_spec (xs : List Nat) (m running answer : Nat) :
    scanMod m running answer xs =
      (answer + running * xs.sum + pairs xs) % m := by
  induction xs generalizing running answer with
  | nil => simp [scanMod, pairs]
  | cons x xs ih =>
    rw [scanMod, ih, strip_mod]
    simp [pairs, List.sum_cons, Nat.mul_add, Nat.add_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem scanMod_correct (xs : List Nat) (m : Nat) :
    scanMod m 0 0 xs = pairs xs % m := by
  simpa using scanMod_spec xs m 0 0

end PairSumCheck
```

An even simpler candidate, [ABC181 B — Trapezoid Sum](https://atcoder.jp/contests/abc181/tasks/abc181_b?lang=en), replaces enumeration of each integer in an interval by an arithmetic-series formula. However, a local Clang `-O2` experiment ran the naive reference at maximum constraints in about 0.4 seconds despite 100 billion iterations at source level. A host compiler can already eliminate that summation loop. Do not choose it as a reliable TLE benchmark without checking the actual target compiler. ABC177 C exhibited the intended runtime gap in the local experiment.

After the first proof, consider [ABC122 C — GeT AC](https://atcoder.jp/contests/abc122/tasks/abc122_c?lang=en), scanning for `AC` versus prefix counts, to exercise ASCII strings. Then use [ABC371 D — 1D Country](https://atcoder.jp/contests/abc371/tasks/abc371_d?lang=en), scanning villages versus prefix sums and binary search, to exercise signed coordinates and reusable search functions. These algorithm choices are proposed designs, not claims that a formal RStmt refinement proof has already been completed.

**Multiple accepted answers are real, but they need not change the initial theorem.** AtCoder's ABC200 D asks for two distinct nonempty subsequences whose sums agree modulo 200 and accepts any qualifying pair. ABC168 C accepts numerical answers within a specified error tolerance. Both are batch problems. This verifies that accepted answers are not always unique; it does not establish how common such problems are or whether the judging code is available as a script. [ABC200 D — Happy Birthday! 2](https://atcoder.jp/contests/abc200/tasks/abc200_d?lang=en), [ABC168 C — : (Colon)](https://atcoder.jp/contests/abc168/tasks/abc168_c?lang=en)

Exact-output refinement is still sufficient if the optimized program reproduces the deterministic reference's chosen answer. It can unnecessarily constrain witness choice, tie-breaking, or floating-point evaluation, so initially choose unique-answer problems. Accepting a different valid witness would require a checker or another acceptance relation; that extension is deferred, rather than hidden inside the current theorem.

Even ordinary unique-answer problems may allow different whitespace. AtCoder documents relaxed whitespace rules, with exceptions. Exact byte equality is a deliberately stronger requirement that avoids modeling those exceptions; a shared canonical printer makes it practical. No assertion is needed that AtCoder literally performs byte equality. [AtCoder whitespace rules](https://atcoder.jp/contests/abc262/rules)

In this proposal, rejection means excluding an input or abandoning the reference's computation. An optional internal check before output can also reject if the reference detects that its own result is invalid. The framework does not ask the reference to consume and judge the optimized program's answer. The accepted-output specification is simply whatever the trusted reference successfully emits.

**Local verification supports the design, with explicit limits.** Experiments were run on 2026-09-08 using Lean 4.29.0-rc1 and Apple Clang 21.0.0 on arm64 macOS. The full algebra block above was extracted from this document and checked with Lean, including the append lemma connecting the pair sum to the prefix-based loop invariant.

The existing executable interpreter `Stmt.interp` uses fuel to make test execution terminate; the relational `BigStep` semantics does not. Exhausting interpreter fuel reports an inconclusive test, not semantic rejection or proof of divergence. Interpreter soundness and completeness connect successful test executions to the fuel-free relation. Fuel is not part of the benchmark theorem.

- A standalone Lean relational model checked reflexivity and transitivity of refinement, removal of a pure domain guard, composition with a common parser relation, vacuity for an always-rejecting reference, and impossibility of replacing a successful reference with rejection or a different output. These are generic relational results, not a proof about the future extended RStmt implementation.
- Six executable Lean guards against the current Radix code confirmed that both `return 0` and `return 1` are reported as success, both logical operators eagerly evaluate an invalid right operand, a boolean-tagged allocation contains an unsigned zero, and a block-local declaration remains accessible afterward.
- Nine standalone scanner cases checked unsigned boundaries, leading zeros, malformed tokens, signs, missing tokens, and extra input. An additional rejection experiment confirmed that printed bytes remain observable when a later validation fails; output alone is not successful completion.
- C++ ABC177 C prototypes compiled with `clang++ -std=c++20 -O2 -Wall -Wextra -Werror`. Both passed the two official samples, 200 randomized cases, and four boundary cases. At `N = 200000`, the optimized output matched an independent Python exact-integer oracle in approximately 0.024 seconds including input serialization; the reference exceeded a local two-second timeout. These prototypes used standard numeric input to isolate the algorithm comparison, allocated their arrays once, and did not deallocate them. They did not validate the proposed shared scanner or a C++/RStmt correspondence. The measurements are local evidence, not AtCoder verdicts.

These experiments establish feasibility and identify implementation gaps. Their scratch files are not required handoff artifacts. Recreate durable, reproducible checks as part of implementation. Only this proposal has been changed in the project so far; the revised language and the benchmark proof have not been implemented. The full repository test suite was not rerun for the documentation changes.

**The implementation agent should use the existing library as the starting point.** The repository pins Lean 4.29.0-rc1 in `lean-toolchain`. `Radix.lean` imports the core modules, optimization proofs, examples, and tests; `lake build Radix` is the focused library build. The default `lake build` builds the slide executable, and should also work when the handoff is complete. Keep the pinned toolchain unless a concrete dependency requires a change. Inspect and repair affected imports rather than dropping unrelated tests or proofs to obtain a green build.

Change the AST, evaluators, and associated proofs coherently. Keep the five existing optimizer passes and their appropriate correctness results, updating them for short-circuiting, I/O, and rejection. Removing obsolete free/linearity cases is expected. Old quotation spellings may be migrated or retained as internal test convenience, but they are not an alternative source for the benchmark theorem. General runtime strings, signed integers, arbitrary C++ function declarations, calls returning values, a verified native compiler, verified runtime-library internals, and more benchmarks are outside the required deliverable. The first source frontend may support just `void solve()` plus the fixed primitive helpers, while the existing internal function/call semantics must still propagate rejection correctly.

Suggested artifact locations are below; names can be adjusted to fit the implementation, with the actual paths and build commands documented:

```text
Radix/Frontend/Cpp.lean              subset parser, checking, name resolution
Radix/Proofs/Refinement.lean         successful execution and refinement API
Radix/Benchmarks/ABC177C.lean        embedded source bytes, parsing evidence, proof
runtime/radix_io.hpp                shared helper implementation, embedded on export
benchmarks/abc177c/reference.cpp     standalone source bound to the proof
benchmarks/abc177c/optimized.cpp     standalone source bound to the proof
scripts/check_abc177c.py             reproducible native tests and performance check
```

The `.cpp` files must be standalone: the prelude is included in the submitted bytes, rather than requiring AtCoder to locate `runtime/radix_io.hpp`. The benchmark proof artifact should bind source bytes to parsed programs explicitly. For example, expose equations of the form `parseSubmission referenceSource = .ok reference` and `parseSubmission optimizedSource = .ok optimized`, alongside `Refines reference optimized`. Parsing evidence for the concrete files can be generated mechanically. Reparse and rebuild when either source or the prelude changes. Do not prove a manually constructed AST equivalent to another AST while merely asserting that separate source files implement them.

The first theorem is a proof in Radix's subset semantics, with the parser/C++ correspondence and runtime contract documented as shared trust boundaries. This is the agreed stopping point for formal scope. Do not insert `sorry`, `admit`, or new axioms assuming benchmark correctness. Optional future work can reduce those trust boundaries or broaden the language; it is not needed to complete the milestones below.

**Milestones, in implementation order:**

1. **Remove linearity and deallocation.** Delete the experimental linearity module, its dedicated tests and imports, and the `Stmt.free` constructor with its syntax and evaluation rules. Remove obsolete deallocation cases from optimizer traversals and proofs, migrate affected examples, and keep ordinary typing and array aliasing. Prove that allocations remain present and retain their lengths across successful execution. Completion: `lake build Radix` passes, active language paths cannot free storage, and a test shows that copying an array reference preserves shared writes. Do not add another ownership checker.

2. **Establish the execution and refinement interfaces.** Add explicit rejection, separate it from runtime faults and interpreter fuel exhaustion, and define fuel-free `RunsSuccessfully` and `Refines`. Make program success depend on complete successful termination. Implement short-circuit `&&` and `||`, update affected proofs, and thread rejection through calls and all control-flow constructs. Completion: determinism and interpreter soundness/completeness hold for the revised constructs; generic refinement reflexivity/transitivity are proved; tests distinguish an accepted program, a rejected program, an invalid access, and an inconclusive fuel-limited run. A rejection in a callee cannot be swallowed, and a skipped logical operand is not evaluated.

3. **Model and implement the shared I/O primitives.** Add input bytes, cursor, and output bytes to state; implement the specified reader, unsigned writer, literal writer, EOF check, and rejection helper in the logical semantics and interpreter. Implement the shared native prelude with the same contracts. Update state-threading lemmas and optimizer cases: reads change destinations and stream position, and writes/rejection are observable effects. Completion: the library build and relevant proofs pass; tests cover zero, the maximum unsigned value, overflow, signs, malformed tokens, supported whitespace, missing input, trailing input, and output followed by rejection. No function error restores an earlier I/O state. The native prelude compiles with warnings enabled.

4. **Parse the actual C++ submission subset.** Implement the dedicated grammar, statement checking, unique local-name resolution, and exact prelude/wrapper handling. Cover the first benchmark's `u64` scalars and arrays, boolean conditions, `ULL` literals, pure arithmetic and indexing, declarations, assignment, loops, and primitive helper statements. Reject unsupported syntax and undeclared or incorrectly typed uses. Completion: representative source files parse to checked programs and compile as C++; precedence, shadowing, declaration re-entry in loops, and short-circuit cases are tested. Standalone export/import preserves the exact source bytes associated with the proof, and a changed source or prelude requires new parsing evidence. No separate handwritten algorithm translation is involved.

5. **Produce both executable ABC177 C programs.** Write the complete reference and running-sum implementations described above, including identical input validation, allocation, EOF checking, and final decimal/newline output. Embed or import their exact standalone source files into Lean, with successful parsing equations. Completion: both compile and pass the two official samples and small independent-oracle cases; malformed input and domain violations explicitly reject. The benchmark uses no deallocation, no linearity checker, and no problem-specific unverified I/O adapter. This milestone establishes executable artifacts, not yet their equivalence proof.

6. **Prove the complete ABC177 C refinement.** Connect the scalar invariants and algebra above to the actual parsed RStmt loops. Prove the reference's inner and outer loop behavior, the optimized running-sum invariant, array bounds, termination on successful reference inputs, and the unsigned arithmetic bounds needed for the modulo argument. Compose these with the shared input and output code. Completion: a kernel-checked theorem with exactly the common `Refines reference optimized` shape holds for the programs parsed from the files, without a separately supplied problem-domain predicate. No full-state equality is required, no testing fuel appears in the theorem, and the theorem does not leave optimized termination conditional on an additional assumption. Include the benchmark module in the normal proof build and inspect its axiom dependencies.

7. **Validate and package the handoff result.** Add a reproducible command that builds the proof and compiles/tests the same source artifacts. Exercise samples, randomized and boundary inputs, and the maximum-size case; compare against an independent exact-integer oracle and record the reference/optimized runtime gap with compiler and platform details. Run `lake build Radix` and the default `lake build`, repairing affected documentation and slide examples. Completion: the standalone optimized source is ready to submit, the proof/source/prelude identities and commands are recorded, and the README states the theorem and remaining shared trust boundaries accurately. Local performance evidence must be labeled as local; actual AtCoder verdicts are recorded only if submission access and authorization are available. Lack of such access does not block the source-and-proof deliverable. End with a status report for these seven milestones, including any uncompleted work rather than presenting partial results as complete.
