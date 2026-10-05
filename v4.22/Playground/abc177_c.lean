import Std
import Batteries

def modulus : Int := 10^9 + 7

def ans4 (A : Array Int) : Int :=
  let initial : Int × Int := (0, A.foldl (· + ·) 0)

  let (ret, _) := A.foldl
    (fun (ret, cofactor) a =>
      let cofactor := cofactor - a
      (ret + a * cofactor, cofactor))
    initial

  ret % modulus

def main : IO Unit := do
  let stdin ← IO.getStdin
  let _ ← stdin.getLine  -- Discard the first line.
  let line := (← stdin.getLine).trim
  let A := (line.splitOn " ").toArray.map String.toInt!
  IO.println (ans4 A)

-- #eval ans4 #[141421356,17320508,22360679,244949]
