import Mathlib

set_option maxRecDepth 3000000

open Lean Meta in
unsafe def evalNatExpr (e : Expr) : MetaM (Option Nat) := do
  let ty ← inferType e
  let .const ``Nat _ := ty | return none
  let val ← Lean.Meta.evalExpr Nat (mkConst ``Nat) e
  return some val

open Lean Meta Elab Tactic in
elab "fast_decide" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let proof ← mkDecideProof goalType
  goal.assign proof

#reduce (List.range 1000).sum

theorem fast_decide_1k : ((List.range 1000).filter (· % 2 == 0)).sum = 249500 := by fast_decide
#print fast_decide_1k
#print axioms fast_decide_1k

theorem decide_1k : ((List.range 1000).filter (· % 2 == 0)).sum = 249500 := by decide
#print decide_1k

example : ((List.range 10000).filter (· % 2 == 0)).sum = 24995000 := by fast_decide
example : ((List.range 100000).filter (· % 2 == 0)).sum = 2499950000 := by fast_decide
example : ((List.range 1000000).filter (· % 2 == 0)).sum = 249999500000 := by fast_decide

section TermMode

example : ((List.range 1000).filter (· % 2 == 0)).sum = 249500 :=
  of_decide_eq_true (by rfl)

example : ((List.range 10000).filter (· % 2 == 0)).sum = 24995000 :=
  of_decide_eq_true (by rfl)

-- example : ((List.range 100000).filter (· % 2 == 0)).sum = 2499950000 :=
--   of_decide_eq_true (by rfl)

-- example : ((List.range 1000000).filter (· % 2 == 0)).sum = 249999500000 :=
--   of_decide_eq_true (by rfl)

end TermMode

/-! ## Chunked decide: split large ranges into small pieces -/

/-- Sum of `(List.range len).map (offset + ·) |>.filter p` -/
def rangeFilterSum (p : Nat → Bool) (offset len : Nat) : Nat :=
  (((List.range len).map (offset + ·)).filter p).sum

theorem rangeFilterSum_base (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).sum = rangeFilterSum p 0 n := by
  simp [rangeFilterSum]

theorem rangeFilterSum_add (p : Nat → Bool) (offset m n : Nat) :
    rangeFilterSum p offset (m + n) =
    rangeFilterSum p offset m + rangeFilterSum p (offset + m) n := by
  simp only [rangeFilterSum, List.range_add, List.map_append, List.map_map,
             List.filter_append, List.sum_append]
  congr 1; congr 1; congr 1; ext x; simp

open Lean Meta in
simproc_decl chunkReduce (rangeFilterSum _ _ _) := fun e => do
  let .app (.app (.app (.const ``rangeFilterSum _) p) offset) len := e
    | return .continue
  let some lenVal ← unsafe evalNatExpr len | return .continue
  if lenVal ≤ 1000 then
    let some val ← unsafe evalNatExpr e | return .continue
    let result := mkNatLit val
    let proof ← mkDecideProof (← mkEq e result)
    return .done { expr := result, proof? := some proof }
  else
    let m := lenVal / 2
    let n := lenVal - m
    let mLit := mkNatLit m
    let nLit := mkNatLit n
    let rfs := mkConst ``rangeFilterSum
    let lhs := mkApp (mkApp (mkApp rfs p) offset) mLit
    let newOffset ← mkAppM ``HAdd.hAdd #[offset, mLit]
    let rhs := mkApp (mkApp (mkApp rfs p) newOffset) nLit
    let result ← mkAppM ``HAdd.hAdd #[lhs, rhs]
    let proof := mkApp (mkApp (mkApp (mkApp (mkConst ``rangeFilterSum_add) p) offset) mLit) nLit
    return .done { expr := result, proof? := some proof }

macro "chunk_decide" : tactic =>
  `(tactic| (rw [rangeFilterSum_base]; simp only [chunkReduce]))

section ChunkTests

example : ((List.range 1000).filter (· % 2 == 0)).sum = 249500 := by chunk_decide

example : ((List.range 10000).filter (· % 2 == 0)).sum = 24995000 := by chunk_decide

example : ((List.range 100000).filter (· % 2 == 0)).sum = 2499950000 := by chunk_decide

-- example : ((List.range 1000000).filter (· % 2 == 0)).sum = 249999500000 := by chunk_decide

end ChunkTests

/-! ## Chunked countP: split large ranges into small pieces -/

/-- countP of `(List.range len).map (offset + ·)` -/
def rangeCountP (p : Nat → Bool) (offset len : Nat) : Nat :=
  ((List.range len).map (offset + ·)).countP p

theorem rangeCountP_base (p : Nat → Bool) (n : Nat) :
    (List.range n).countP p = rangeCountP p 0 n := by
  simp [rangeCountP]

theorem Nat.count_eq_rangeCountP (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    Nat.count p n = rangeCountP (fun k => decide (p k)) 0 n := by
  simp [Nat.count, rangeCountP]

theorem rangeCountP_add (p : Nat → Bool) (offset m n : Nat) :
    rangeCountP p offset (m + n) =
    rangeCountP p offset m + rangeCountP p (offset + m) n := by
  simp only [rangeCountP, List.range_add, List.map_append, List.map_map,
             List.countP_append]
  congr 1; congr 1; congr 1; ext x; simp; grind

open Lean Meta in
simproc_decl chunkCountPReduce (rangeCountP _ _ _) := fun e => do
  let .app (.app (.app (.const ``rangeCountP _) p) offset) len := e
    | return .continue
  let some lenVal ← unsafe evalNatExpr len | return .continue
  if lenVal ≤ 1000 then
    let some val ← unsafe evalNatExpr e | return .continue
    let result := mkNatLit val
    let proof ← mkDecideProof (← mkEq e result)
    return .done { expr := result, proof? := some proof }
  else
    let m := lenVal / 2
    let n := lenVal - m
    let mLit := mkNatLit m
    let nLit := mkNatLit n
    let rcp := mkConst ``rangeCountP
    let lhs := mkApp (mkApp (mkApp rcp p) offset) mLit
    let newOffset ← mkAppM ``HAdd.hAdd #[offset, mLit]
    let rhs := mkApp (mkApp (mkApp rcp p) newOffset) nLit
    let result ← mkAppM ``HAdd.hAdd #[lhs, rhs]
    let proof := mkApp (mkApp (mkApp (mkApp (mkConst ``rangeCountP_add) p) offset) mLit) nLit
    return .done { expr := result, proof? := some proof }

macro "chunk_count" : tactic =>
  `(tactic| (rw [Nat.count_eq_rangeCountP]; simp only [chunkCountPReduce]))

section CountTests

example : Nat.count Nat.Prime 10 = 4 := by chunk_count

example : Nat.count Nat.Prime 1000 = 168 := by chunk_count

example : Nat.count Nat.Prime 10000 = 1229 := by chunk_count

end CountTests
