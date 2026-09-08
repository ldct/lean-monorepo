import Radix.Frontend.Cpp
import Radix.Eval.Interp

/-! Source-level regressions also checked against native C++20 with the fixed
prelude. These tests exercise lexical boundaries and C++ precedence. -/
namespace Radix.Cpp.CorrespondenceTests

private def outputOf (source : String) : Option String := do
  let p ← (parseSolve source).toOption
  let state ← (p.run 1000).toOption
  String.fromUTF8? state.output

#guard outputOf "void solve() { u64 x = 9ULL - -2ULL * 3ULL; write_u64(x); }" == some "15"
#guard outputOf "void solve() { u64 x = -1ULL / 2ULL; write_u64(x); }" == some "9223372036854775807"
#guard outputOf "void solve() { u64 x = 18446744073709551615ULL + 2ULL; write_u64(x); }" == some "1"
#guard outputOf "void solve() { bool x = false || true && false; if (x) { write_text(\"bad\"); } else { write_text(\"ok\"); } }" == some "ok"
#guard outputOf "void solve() { bool x = !false == true; if (x) { write_text(\"ok\"); } }" == some "ok"
#guard outputOf "void solve() { bool x = 1ULL + 2ULL * 3ULL == 7ULL && 9ULL % 4ULL == 1ULL; if (x) { write_text(\"ok\"); } }" == some "ok"
#guard outputOf "void solve() { write_text(\"quote:\\\" slash:\\\\ tab:\\t newline:\\n\"); }" == some "quote:\" slash:\\ tab:\t newline:\n"
#guard outputOf "void solve() { write_text(\"before\"); return; write_text(\"after\"); }" == some "before"
#guard outputOf "void solve() { u64* a = new u64[1ULL](); { u64* b = a; b[0ULL] = 8ULL; } write_u64(a[0ULL]); }" == some "8"
#guard outputOf "void solve() { u64 z = 0ULL; bool b = false && (1ULL / z == 1ULL); bool c = true || (1ULL / z == 1ULL); if (!b && c) { write_text(\"ok\"); } }" == some "ok"

private def rejects (body : String) : Bool :=
  !(parseSolve ("void solve() { " ++ body ++ " }")).isOk

#guard rejects "u64 x = 0x10ULL;"
#guard rejects "u64 x = 1e3ULL;"
#guard rejects "u64 x = 1ULLfoo;"
#guard rejects "u64 x = 1UL;"
#guard rejects "u64 x = -1;"
#guard rejects "u64 x = 1ULL; x = ++x;"
#guard rejects "u64 x = 1ULL; x = x++ + 1ULL;"
#guard rejects "u64 x = 1ULL; write_u64(x = 2ULL);"
#guard rejects "bool x = true; read_u64(x);"
#guard rejects "u64* a = new u64[1ULL](); read_u64(a);"
#guard rejects "u64* a = new u64[1ULL](); write_u64(a);"
#guard rejects "u64 x = 0ULL; write_text(x);"
#guard rejects "u64* a = new u64[1ULL](); bool b = a == a;"
#guard rejects "u64 x = 1ULL; bool b = x == true;"
#guard rejects "u64 x = 1ULL; x = !x;"
#guard rejects "u64 x = 1ULL; bool b = (x < 2ULL) < 3ULL;"
#guard rejects "u64 x = 0ULL; write_u64(read_u64(x));"
#guard rejects "u64 x = 1ULL; { bool x = false; x = 2ULL; }"

end Radix.Cpp.CorrespondenceTests
