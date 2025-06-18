import Std.Internal.Parsec.String
import Std.Internal.Parsec

namespace Day03
open Std.Internal.Parsec.String
open Std.Internal.Parsec (skip many many1 attempt)

structure MulInstruction where
  a : Nat
  b : Nat
  deriving Repr

def pmulInstruction : Parser MulInstruction := do
  skipString "mul("
  let a ← digits
  skipChar ','
  let b ← digits
  skipChar ')'
  return {a, b}
