import Radix.Frontend.Cpp
import Radix.Eval.Interp

namespace Radix.Cpp.Tests
open Radix.Cpp

def accepted (s : String) : Bool := (parseSolve s).isOk
#guard accepted "void solve() { u64 x = 1ULL + 2ULL * 3ULL; write_u64(x); }"
#guard accepted "void solve() { bool b = false && (1ULL / 0ULL == 0ULL); if (b) { reject(); } }"
#guard accepted "void solve() { u64 x = 1ULL; { u64 x = 2ULL; write_u64(x); } write_u64(x); }"
#guard accepted "void solve() { u64 i = 0ULL; while (i < 3ULL) { u64 x = 1ULL; i = i + x; } }"
#guard accepted "void solve() { u64* a = new u64[2ULL](); u64* b = a; b[0ULL] = 3ULL; write_u64(a[0ULL]); }"
#guard !accepted "void solve() { x = 0ULL; }"
#guard !accepted "void solve() { u64 x = 0; }"
#guard !accepted "void solve() { u64 x; }"
#guard !accepted "void solve() { u64 x = x; }"
#guard !accepted "void solve() { u64 x = 1ULL; { u64 x = x; } }"
#guard !accepted "void solve() { { u64 x = 0ULL; } write_u64(x); }"
#guard !accepted "void solve() { u64 x = 0ULL; x = true; }"
#guard !accepted "void solve() { u64* a = new u64[1ULL](); delete[] a; }"
#guard !accepted "void solve() { u64* a = new u64[1ULL](); a = a + 1ULL; }"
#guard !accepted "void solve() { u64 x = 18446744073709551616ULL; }"
#guard !accepted "void solve() { u64 x = 012ULL; }"
#guard !accepted "void solve() { u64 x = 2ULL; x = x--1ULL; }"
#guard !accepted "void solve() { u64 radix_space = 0ULL; }"
#guard !accepted "void solve() { u64 EOF = 0ULL; }"
#guard !accepted "void solve() { u64 NULL = 0ULL; }"
#guard !accepted "void solve() { u64 EXIT_FAILURE = 0ULL; }"
#guard !accepted "void solve() { u64 sa_handler = 0ULL; }"
#guard !accepted "void solve() { u64 myVar = 0ULL; }"
#guard !accepted "void solve() { u64 errno = 0ULL; }"
#guard !accepted "void solve() { u64 switch = 0ULL; }"
#guard !accepted "void solve() { u64 reject = 0ULL; }"
#guard !accepted "void solve() { if (1ULL) { return; } }"

-- Inspect the parsed tree, independent of the evaluator, to check C++ precedence
-- and associativity as well as distinct local IDs for lexical shadowing.
#guard match parseSolve "void solve() { u64 x = 8ULL - 3ULL - 1ULL; }" with
  | .ok ⟨[], .block [.decl "x$0" .uint64 (.binop .sub (.binop .sub _ _) _)]⟩ => true
  | _ => false
#guard match parseSolve "void solve() { u64 x = 1ULL + 2ULL * 3ULL; }" with
  | .ok ⟨[], .block [.decl _ _ (.binop .add _ (.binop .mul _ _))]⟩ => true
  | _ => false
#guard match parseSolve "void solve() { u64 x = 1ULL; { u64 x = 2ULL; } write_u64(x); }" with
  | .ok ⟨[], .block [.decl "x$0" _ _, .block [.decl "x$1" _ _], .writeU64 (.var "x$0")]⟩ => true
  | _ => false
#guard (parseSubmission (trustedPrelude ++ "\nvoid solve() {}\n" ++ wrapper)).isOk
#guard !(parseSubmission (trustedPrelude ++ "\n#define N 3\nvoid solve() {}\n" ++ wrapper)).isOk
#guard !(parseSubmission (trustedPrelude ++ "\nvoid solve() {}\nint main() { return 1; }\n")).isOk
#guard !(parseSubmission ("// changed prelude\n" ++ trustedPrelude ++ "\nvoid solve() {}\n" ++ wrapper)).isOk

def outputOf (source : String) : Option String := do
  let p ← (parseSolve source).toOption
  let σ ← (p.run 1000).toOption
  String.fromUTF8? σ.output

#guard outputOf "void solve() { u64 i = 0ULL; while (i < 3ULL) { u64 x = 1ULL; write_u64(x); x = 9ULL; i = i + 1ULL; } }" == some "111"
#guard outputOf "void solve() { bool b = false && (1ULL / 0ULL == 0ULL); bool c = true || (1ULL / 0ULL == 0ULL); if (b || !c) { reject(); } write_text(\"ok\"); }" == some "ok"
#guard outputOf "void solve() { u64 x = 1ULL; { u64 x = 2ULL; write_u64(x); } write_u64(x); }" == some "21"
#guard outputOf "void solve() { u64* a = new u64[1ULL](); u64* b = a; b[0ULL] = 7ULL; write_u64(a[0ULL]); }" == some "7"

end Radix.Cpp.Tests
