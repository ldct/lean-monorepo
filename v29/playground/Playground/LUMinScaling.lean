/-!
# Exact Minimal Scaling for LU Decomposition

Given a non-singular rational matrix A that admits a pivotless LU decomposition,
find the smallest positive integer n such that nA = L'U' where L' is lower-triangular
with integer entries and U' is upper-triangular with integer entries.

Also computes a leading-minor bound and verifies it on random matrices.

This is a direct port of the Python/SymPy program.
-/

-- ============================================================
-- Basic utilities
-- ============================================================

partial def Nat.gcd' (a b : Nat) : Nat :=
  if b == 0 then a else Nat.gcd' b (a % b)

def Int.gcd' (a b : Int) : Nat :=
  Nat.gcd' a.natAbs b.natAbs

def Nat.lcm' (a b : Nat) : Nat :=
  if a == 0 || b == 0 then 0 else a / Nat.gcd' a b * b

def gcdList (xs : List Int) : Nat :=
  xs.foldl (fun acc x => Int.gcd' (acc : Int) x) 0

def lcmList (xs : List Int) : Nat :=
  xs.foldl (fun acc x => Nat.lcm' acc x.natAbs) 1

-- ============================================================
-- Rat (ℚ) matrix type: row-major List (List Rat)
-- ============================================================

abbrev QMat := List (List Rat)

namespace QMat

def rows (m : QMat) : Nat := m.length
def cols (m : QMat) : Nat := (m[0]?.map List.length).getD 0

def get (m : QMat) (i j : Nat) : Rat :=
  (m[i]?.bind (·[j]?)).getD 0

def set (m : QMat) (i j : Nat) (v : Rat) : QMat :=
  m.zipIdx.map fun ⟨row, ri⟩ =>
    if ri == i then row.zipIdx.map fun ⟨val, ci⟩ => if ci == j then v else val
    else row

def identity (n : Nat) : QMat :=
  List.range n |>.map fun i =>
    List.range n |>.map fun j =>
      if i == j then 1 else 0

def zeros (r c : Nat) : QMat :=
  List.replicate r (List.replicate c 0)

def diag (ds : List Rat) : QMat :=
  let n := ds.length
  List.range n |>.map fun i =>
    List.range n |>.map fun j =>
      if i == j then ds.getD i 0 else 0

def scale (s : Rat) (m : QMat) : QMat :=
  m.map (·.map (s * ·))

def mul (a b : QMat) : QMat :=
  let n := a.rows
  let p := b.cols
  let m_inner := a.cols
  List.range n |>.map fun i =>
    List.range p |>.map fun j =>
      List.range m_inner |>.foldl (fun acc k => acc + a.get i k * b.get k j) 0

def eq (a b : QMat) : Bool :=
  a.rows == b.rows && a.cols == b.cols &&
  (List.range a.rows).all fun i =>
    (List.range a.cols).all fun j =>
      a.get i j == b.get i j

def showRat (q : Rat) : String := ToString.toString q

def toString (m : QMat) : String :=
  let rows := m.map fun row =>
    "  [" ++ String.intercalate ", " (row.map showRat) ++ "]"
  "[\n" ++ String.intercalate ",\n" rows ++ "\n]"

def submatrix (m : QMat) (rs cs : Nat) : QMat :=
  (m.take rs).map (·.take cs)

def getRow (m : QMat) (i : Nat) : List Rat :=
  (m[i]?).getD []

end QMat

instance : ToString QMat where
  toString m := QMat.toString m

-- ============================================================
-- Determinant (Gaussian elimination, exact over ℚ)
-- ============================================================

partial def detAux (m : QMat) (n : Nat) (sign : Rat) : Rat :=
  if n == 0 then sign
  else if n == 1 then sign * m.get 0 0
  else
    -- Find pivot in column 0
    let pivotRow := (List.range n).find? fun i => m.get i 0 != 0
    match pivotRow with
    | none => 0
    | some pr =>
      let sign' := if pr == 0 then sign else -sign
      -- Swap row 0 and pivotRow
      let m' := if pr == 0 then m
        else
          let row0 := m.getRow 0
          let rowP := m.getRow pr
          m.zipIdx.map fun ⟨row, i⟩ =>
            if i == 0 then rowP else if i == pr then row0 else row
      let pivot := m'.get 0 0
      -- Eliminate column 0 from rows 1..n-1
      let m'' := List.range n |>.map fun i =>
        if i == 0 then m'.getRow 0
        else
          let factor := m'.get i 0 / pivot
          List.range (QMat.cols m') |>.map fun j =>
            m'.get i j - factor * m'.get 0 j
      -- Recurse on (n-1)×(n-1) submatrix (rows 1.., cols 1..)
      let sub := (m''.drop 1).map (·.drop 1)
      detAux sub (n - 1) (sign' * pivot)

def det (m : QMat) : Rat := detAux m m.rows 1

-- ============================================================
-- LU decomposition (Doolittle, no pivoting)
-- ============================================================

structure LUResult where
  L : QMat
  U : QMat
  ok : Bool  -- false if pivot was zero (needs permutation)
deriving Nonempty

partial def luDecompose (A : QMat) : LUResult :=
  let n := A.rows
  let L := QMat.identity n
  let U := QMat.zeros n n
  let rec go (k : Nat) (L U : QMat) : LUResult :=
    if k >= n then { L, U, ok := true }
    else
      -- U[k][j] = A[k][j] - sum_{s<k} L[k][s]*U[s][j]
      let U' := (List.range n).foldl (fun U j =>
        let s := (List.range k).foldl (fun acc s => acc + L.get k s * U.get s j) 0
        U.set k j (A.get k j - s)) U
      let pivot := U'.get k k
      if pivot == 0 then { L, U := U', ok := false }
      else
        -- L[i][k] = (A[i][k] - sum_{s<k} L[i][s]*U[s][k]) / U[k][k]
        let L' := (List.range n).foldl (fun L i =>
          if i <= k then L
          else
            let s := (List.range k).foldl (fun acc s => acc + L.get i s * U'.get s k) 0
            L.set i k ((A.get i k - s) / pivot)) L
        go (k + 1) L' U'
  go 0 L U

-- ============================================================
-- Rat utilities
-- ============================================================

/-- Denominator of a Rat (always positive). -/
def ratDenom (q : Rat) : Int := q.den

/-- Numerator of a Rat. -/
def ratNum (q : Rat) : Int := q.num

/-- Given a row of rationals, find the least positive rational r
    such that r * row is all integers. r = lcm(denoms) / gcd(scaled_ints). -/
def rowMinMultiplier (row : List Rat) : Rat :=
  let ds := row.map (fun q => (ratDenom q : Int))
  let d := lcmList ds
  let ints := row.map fun q => ratNum q * ((d : Int) / ratDenom q)
  let g := gcdList ints
  if g == 0 then 1
  else (d : Rat) / (g : Rat)

-- ============================================================
-- Exact minimal scaling
-- ============================================================

structure MinScalingResult where
  n_min : Nat
  L_int : QMat
  U_int : QMat
  L_rat : QMat
  U_rat : QMat
  a : List Nat
  r : List Rat
  t : List Int

def exactMinScaling (A : QMat) : Option MinScalingResult := do
  let lu : LUResult := luDecompose A
  if !lu.ok then none
  let d := det A
  if d == 0 then none
  let n := A.rows
  let mut aList : List Nat := []
  let mut rList : List Rat := []
  let mut pList : List Int := []
  let mut qList : List Int := []
  for i in List.range n do
    let colDenoms := (List.range n).map fun k => ratDenom (lu.L.get k i)
    let a_i := lcmList colDenoms
    let uRow := (List.range n).map fun j => lu.U.get i j
    let r_i := rowMinMultiplier uRow
    let prod := (a_i : Rat) * r_i
    aList := aList ++ [a_i]
    rList := rList ++ [r_i]
    pList := pList ++ [ratNum prod]
    qList := qList ++ [ratDenom prod]
  let n_min := lcmList pList
  let mut tList : List Int := []
  for i in List.range n do
    let a_i := aList.getD i 0
    let q_i := qList.getD i 1
    let p_i := pList.getD i 1
    tList := tList ++ [(a_i : Int) * q_i * ((n_min : Int) / p_i)]
  let T := QMat.diag (tList.map Rat.ofInt)
  let Tinv := QMat.diag (tList.map (fun (x : Int) => (1 : Rat) / (x : Rat)))
  let L_int := QMat.mul lu.L T
  let U_int := QMat.mul (QMat.scale (n_min : Rat) Tinv) lu.U
  return {
    n_min
    L_int
    U_int
    L_rat := lu.L
    U_rat := lu.U
    a := aList
    r := rList
    t := tList
  }

-- ============================================================
-- Leading minor bound
-- ============================================================

def leadingMinorBound (A : QMat) : Option Nat := do
  let n := A.rows
  if n == 1 then return 1
  let mut deltas : List Int := []
  for k in List.range (n - 1) do
    let k' := k + 1
    let sub := A.submatrix k' k'
    let d := det sub
    if d == 0 then none
    deltas := deltas ++ [((Rat.num d).natAbs : Int)]
  -- terms = [deltas[0]] ++ [deltas[i-1]*deltas[i] for i in 1..n-2] ++ [deltas[-1]]
  let first := deltas.getD 0 1
  let last := deltas.getD (deltas.length - 1) 1
  let mut terms : List Int := [first]
  for i in List.range (deltas.length - 1) do
    let i' := i + 1
    if i' < deltas.length then
      let prev := deltas.getD i 1
      let cur := deltas.getD i' 1
      terms := terms ++ [prev * cur]
  terms := terms ++ [last]
  return lcmList terms

-- ============================================================
-- Simple PRNG (xorshift64)
-- ============================================================

structure Rng where
  state : UInt64

def Rng.new (seed : UInt64) : Rng := { state := seed }

def Rng.next (r : Rng) : Rng × UInt64 :=
  let s := r.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

def Rng.nextBounded (r : Rng) (bound : Nat) : Rng × Nat :=
  let (r', v) := r.next
  (r', (v.toNat % bound))

def Rng.nextIntRange (r : Rng) (lo hi : Int) : Rng × Int :=
  let range := (hi - lo + 1).toNat
  let (r', v) := r.nextBounded range
  (r', lo + v)

-- ============================================================
-- Demo / Main
-- ============================================================

def mkMatrix (rows : List (List Int)) : QMat :=
  rows.map (·.map Rat.ofInt)

def examples : List QMat :=
  [ mkMatrix [[2, 1], [1, 1]]
  , mkMatrix [[2, 0, 0], [0, 1, 0], [0, 0, 1]]
  , mkMatrix [[2, 1, 0], [1, 2, 1], [0, 1, 1]]
  , mkMatrix [[3, 1, 2], [2, 1, 1], [1, 1, 2]]
  ]

def randomMatrix (rng : Rng) (n : Nat) : Rng × QMat :=
  let (rng, rows) := (List.range n).foldl (fun (rng, rows) _ =>
    let (rng, row) := (List.range n).foldl (fun (rng, row) _ =>
      let (rng, v) := rng.nextIntRange (-4) 4
      (rng, row ++ [(v : Rat)])) (rng, ([] : List Rat))
    (rng, rows ++ [row])) ((rng, []) : Rng × QMat)
  (rng, rows)

partial def main : IO Unit := do
  -- Fixed examples
  for A in examples do
    IO.println s!"A ="
    IO.println (ToString.toString A)
    match exactMinScaling A with
    | none => IO.println "  (no pivotless LU or singular)"
    | some data =>
      let bound := (leadingMinorBound A).getD 0
      IO.println s!"n_min = {data.n_min}  leading-minor bound = {bound}"
      IO.println s!"L_int ="
      IO.println (ToString.toString data.L_int)
      IO.println s!"U_int ="
      IO.println (ToString.toString data.U_int)
      let check := QMat.eq (QMat.mul data.L_int data.U_int) (QMat.scale data.n_min A)
      IO.println s!"check: {check}"
    IO.println (String.ofList (List.replicate 60 '-'))

  -- Random trials
  let mut rng := Rng.new 12345
  let mut accepted : Nat := 0
  let mut trials : Nat := 0
  let sizes : Array Nat := #[2, 3, 4, 5]
  let mut ratioSum : Rat := 0
  let mut ratios : Array Rat := #[]
  while accepted < 100 && trials < 20000 do
    trials := trials + 1
    let (rng', sizeIdx) := rng.nextBounded sizes.size
    rng := rng'
    let n := sizes.getD sizeIdx 3
    let (rng', A) := randomMatrix rng n
    rng := rng'
    let d := det A
    if d == 0 then continue
    match exactMinScaling A with
    | none => continue
    | some data =>
      match leadingMinorBound A with
      | none => continue
      | some bound =>
        let check := QMat.eq (QMat.mul data.L_int data.U_int) (QMat.scale data.n_min A)
        if !check then
          IO.println s!"FAILED CHECK for A = {A}"
          continue
        let ratio := (bound : Rat) / (data.n_min : Rat)
        ratioSum := ratioSum + ratio
        ratios := ratios.push ratio
        accepted := accepted + 1

  IO.println s!"Verified {accepted} random matrices."
  if accepted > 0 then
    let avg := ratioSum / (accepted : Rat)
    let sorted := ratios.toList.mergeSort (· ≤ ·)
    let median := sorted.getD (sorted.length / 2) 0
    let avgF := Float.ofInt avg.num / Float.ofInt avg.den
    IO.println s!"Average bound/exact ratio: {avgF}"
    IO.println s!"Median bound/exact ratio: {median}"
