import Radix.Frontend.Cpp
import Radix.Frontend.ASTEquality
import Radix.Eval.Interp

/-! Exact standalone ABC177 C artifacts. The parser checks the embedded runtime
and entry wrapper before lowering the algorithm. These equations bind the
executable tests to the same bytes compiled by scripts/check_abc177c.py.

The complete machine-level refinement is proved in ABC177CRefinement.
Parsing and sample execution are separate from that proof.
-/
namespace Radix.Benchmarks.ABC177C
open Radix.Cpp

def referenceSource : String := cpp_file% "benchmarks/abc177c/reference.cpp"
def optimizedSource : String := cpp_file% "benchmarks/abc177c/optimized.cpp"

-- Emit the checked parse at elaboration time, retaining a transparent AST.
-- The equations below use native_decide for parsing. The generated per-certificate
-- axioms reference_parses._native.native_decide.ax_1_1 and
-- optimized_parses._native.native_decide.ax_1_1 belong to the documented trusted
-- frontend boundary; the algorithmic refinement proof does not use them.
def reference : Program := cpp_program% "benchmarks/abc177c/reference.cpp"
def optimized : Program := cpp_program% "benchmarks/abc177c/optimized.cpp"

theorem reference_parses : parseSubmission referenceSource = .ok reference := by native_decide

theorem optimized_parses : parseSubmission optimizedSource = .ok optimized := by native_decide

def referenceStatements : List Stmt := match reference.main with | .block ss => ss | _ => []
def optimizedStatements : List Stmt := match optimized.main with | .block ss => ss | _ => []
def prefixStatements : List Stmt := referenceStatements.take 9
def inputPrefix : Stmt := .block prefixStatements
def referenceLoop : Stmt := referenceStatements[10]!
def optimizedLoop : Stmt := optimizedStatements[11]!
def outputSuffix : Stmt := .block (referenceStatements.drop 11)

theorem common_prefix : optimizedStatements.take 9 = prefixStatements := by rfl
theorem common_output : optimizedStatements.drop 12 = referenceStatements.drop 11 := by rfl

private def output (p : Program) (input : String) : Option String := do
  let state ← (p.run 10000 input.toUTF8).toOption
  String.fromUTF8? state.output

#guard output reference "3\n1 2 3\n" == some "11\n"
#guard output optimized "3\n1 2 3\n" == some "11\n"
#guard output reference "4\n141421356 17320508 22360679 244949\n" == some "437235829\n"
#guard output optimized "4\n141421356 17320508 22360679 244949\n" == some "437235829\n"
#guard output reference "2\n0 1000000000\n" == some "0\n"
#guard output optimized "2\n1000000000 1000000000\n" == some "49\n"
#guard !(reference.run 1000 "1\n0\n".toUTF8).isOk
#guard !(optimized.run 1000 "2\n1 1000000001\n".toUTF8).isOk
#guard !(reference.run 1000 "2\n1 2 trailing\n".toUTF8).isOk
#guard !(optimized.run 1000 "2\n+1 2\n".toUTF8).isOk

end Radix.Benchmarks.ABC177C
