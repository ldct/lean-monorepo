import Playground.RMQ.Basic

/-- Parse the next natural number from `bytes` starting at position `pos`,
    skipping leading whitespace. Returns (value, newPos). -/
private def readNat (bytes : ByteArray) (pos : Nat) : Nat × Nat := Id.run do
  let size := bytes.size
  -- skip whitespace
  let mut p := pos
  while p < size do
    let b := bytes.get! p
    if b == 0x20 || b == 0x0A || b == 0x0D then p := p + 1
    else break
  -- read digits
  let mut val := 0
  while p < size do
    let b := bytes.get! p
    if 0x30 ≤ b && b ≤ 0x39 then
      val := val * 10 + (b - 0x30).toNat
      p := p + 1
    else break
  return (val, p)

/-- Iterative sparse table build — equivalent to `SparseTable.make` but avoids
    deep recursion (the library `tickMap` recurses N times for proof convenience). -/
private def buildSparseTable (a : Array ℕ) : Array (Array ℕ) :=
  if a.size == 0 then #[]
  else Id.run do
    let k := Nat.log 2 a.size
    let mut table : Array (Array ℕ) := #[a]
    for m in [:k] do
      let half := 2 ^ m
      let rowLen := a.size - 2 ^ (m + 1) + 1
      let mut row : Array ℕ := Array.mkEmpty rowLen
      for j in [:rowLen] do
        row := row.push (min table[m]![j]! table[m]![j + half]!)
      table := table.push row
    return table

open Cslib.Algorithms.Lean.TimeM in
def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let bytes := input.toUTF8
  -- Parse N and Q
  let (n, pos) := readNat bytes 0
  let (q, pos) := readNat bytes pos
  -- Parse array
  let mut arr : Array ℕ := Array.mkEmpty n
  let mut pos := pos
  for _ in [:n] do
    let (v, p) := readNat bytes pos
    arr := arr.push v
    pos := p
  -- Build sparse table (iterative, avoids stack overflow)
  let table := buildSparseTable arr
  -- Answer queries
  let mut checksum : ℕ := 0
  for _ in [:q] do
    let (l, p) := readNat bytes pos
    let (r, p) := readNat bytes p
    let len := r - l + 1
    let k := Nat.log 2 len
    checksum := checksum + min (table[k]![l]! : ℕ) table[k]![r + 1 - 2 ^ k]!
    pos := p
  IO.println s!"{checksum}"
