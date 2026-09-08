import Radix.Eval.Interp

namespace Radix.Tests.IO
open Radix
private instance : BEq (Except InterpError (Option Value)) where
  beq a b := match a, b with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false


private def scan (s : String) := (ByteIO.readU64 s.toUTF8 0).1
#guard scan "0" == some 0
#guard scan "00042 " == some 42
#guard scan "18446744073709551615" == some 18446744073709551615
#guard scan "18446744073709551616" == none
#guard scan "+1" == none
#guard scan "-1" == none
#guard scan "12x" == none
#guard scan "" == none
#guard scan " \t\n\r" == none
#guard scan "\t\n\x0b\x0c\r 7" == some 7
#guard ByteIO.readU64 "12  34".toUTF8 0 == (some 12, 3)
#guard ByteIO.readU64 "12  34".toUTF8 3 == (some 34, 6)
#guard (ByteIO.readU64 (ByteArray.mk #[49, 0, 50]) 0).1 == none
#guard ByteIO.writeU64 0 == "0".toUTF8
#guard ByteIO.writeU64 18446744073709551615 == "18446744073709551615".toUTF8

private def ioProgram : Stmt := .block [
  .decl "n" .uint64 (.lit (.uint64 0)), .readU64 "n", .expectEof,
  .writeU64 (.var "n"), .writeText "\n"]
private def execute (s : Stmt) (input : String := "") (fuel : Nat := 100) :=
  s.interp fuel { input := input.toUTF8 }
#guard (execute ioProgram "0007 \n").1 == .ok none
#guard (execute ioProgram "0007 \n").2.output == "7\n".toUTF8
#guard (execute ioProgram "7 8").1 == .error .rejected
#guard (execute ioProgram "7 8").2.output == ByteArray.empty
#guard (execute (.writeText "prefix" ;; .reject)).1 == .error .rejected
#guard (execute (.writeText "prefix" ;; .reject)).2.output == "prefix".toUTF8
#guard (execute (.arrSet (.lit (.addr 10)) (.lit (.uint64 0)) (.lit (.uint64 1)))).1 ==
  .error (.fault "arrSet: write failed at addr 10 index 0")
#guard (execute (.while (.lit (.bool true)) .skip) "" 10).1 == .error .fuelExhausted

private def bad : Expr := .binop .eq (.binop .div (.lit (.uint64 1)) (.lit (.uint64 0))) (.lit (.uint64 0))
#guard (Expr.binop .and (.lit (.bool false)) bad).eval {} == some (.bool false)
#guard (Expr.binop .or (.lit (.bool true)) bad).eval {} == some (.bool true)
#guard (Expr.binop .and (.lit (.bool true)) bad).eval {} == none
#guard (Expr.binop .or (.lit (.bool false)) bad).eval {} == none

private def rejectingFunction : FunDecl := {
  name := "f"
  params := []
  retTy := .unit
  body := (.writeText "callee" ;; .reject)
}
private def calleeReject : Program := {
  funs := [rejectingFunction]
  main := (.writeText "caller:" ;; .callStmt "f" [] ;; .writeText "unreachable")
}
private def callResult := calleeReject.main.interp 100 (PState.initFromProgram calleeReject)
#guard callResult.1 == .error .rejected
#guard callResult.2.output == "caller:callee".toUTF8
#guard callResult.2.frames.length == 1
#guard (execute (.scope [] [] (.writeText "inline" ;; .reject))).1 == .error .rejected
#guard (execute (.scope [] [] (.writeText "inline" ;; .reject))).2.output == "inline".toUTF8

private def alias : Stmt := .block [
  .alloc "a" .uint64 (.lit (.uint64 1)),
  .decl "b" (.array .uint64) (.var "a"),
  .arrSet (.var "b") (.lit (.uint64 0)) (.lit (.uint64 42)),
  .writeU64 (.arrGet (.var "a") (.lit (.uint64 0)))]
#guard (execute alias).2.output == "42".toUTF8

private def faultFunction : FunDecl := {
  name := "fault"
  params := []
  retTy := .unit
  body := (.writeText "before fault" ;; .writeU64 (.arrGet (.lit (.addr 999)) (.lit (.uint64 0))))
}
private def faultProgram : Program := { funs := [faultFunction], main := .callStmt "fault" [] }
#guard (faultProgram.execute).1 == .error (.fault "write_u64: expected uint64")
#guard (faultProgram.execute).2.output == "before fault".toUTF8

private def readingFunction : FunDecl := {
  name := "read"
  params := []
  retTy := .unit
  body := .block [.decl "x" .uint64 (.lit (.uint64 0)), .readU64 "x", .writeU64 (.var "x")]
}
private def readingProgram : Program := {
  funs := [readingFunction]
  main := (.callStmt "read" [] ;; .callStmt "read" [] ;; .expectEof)
}
#guard (readingProgram.execute "12 34".toUTF8).1 == .ok none
#guard (readingProgram.execute "12 34".toUTF8).2.output == "1234".toUTF8
#guard (readingProgram.execute "12 34".toUTF8).2.cursor == 5
#guard (execute (.while (.lit (.bool true)) (.writeText "once" ;; .reject))).1 == .error .rejected
#guard (execute (.while (.lit (.bool true)) (.writeText "once" ;; .reject))).2.output == "once".toUTF8

end Radix.Tests.IO
