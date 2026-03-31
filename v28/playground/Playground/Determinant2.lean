import Mathlib

def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

variable {n : Type*} [Fintype n] [DecidableEq n] in
lemma my_helper {M : Matrix n n ℤ} {k : ℤ} (i j : n) (a b : ℤ)
    (h : (M.updateRow i (a • M i + b • M j)).det = a * k)
    (hij : i ≠ j := by decide) (ha : a ≠ 0 := by decide) :
    M.det = k := by
  simpa only [M.det_updateRow_add, M.det_updateRow_smul, M.det_updateRow_eq_zero hij.symm,
    M.updateRow_eq_self, add_zero, mul_zero, mul_eq_mul_left_iff, ha, or_false] using h

private def M₁ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

private def M₂ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0, -2,  3, -2,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

private def M₃ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0,  0,  5, -6,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

private def M₄ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0,  0,  5, -6,  0,  0,  0;
      0,  0,  0,  0,  4, -5,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

open Lean Meta in
unsafe def evalNatExpr (e : Expr) : MetaM (Option Nat) := do
  let ty ← inferType e
  let .const ``Nat _ := ty | return none
  let val ← Lean.Meta.evalExpr Nat (mkConst ``Nat) e
  return some val

def e : Lean.Expr := .lit (.natVal 3)

open Qq in
def e' : Lean.Expr := q(3)
#eval evalNatExpr e'

open Qq in
def e'' : Lean.Expr := q(![1, 2, 3, 4, 5, 6, 7, 8])



open Qq in
def e''' : Lean.Expr := q(!![1, 2, 3, 4, 5, 6, 7, 8; 9, 10, 11, 12, 13, 14, 15, 16])

open Lean Meta Qq in
def myFun (e : Expr) : MetaM (Option (Fin 8 → ℤ)) := fun e => do
  return (some ![1, 2, 3, 4, 5, 6, 7, 8])

#eval myFun e'''

#check Matrix.vecCons

variable {a b c d e f g h : ℤ}

#check Matrix.cons_val
example : ![a] 0 = a := by dsimp only [Matrix.cons_val]

open Lean Meta Qq in
simproc_decl my_simproc (M₄ _) := fun e => do
  let row ← unsafe evalExpr (Fin 8 → ℤ) ( q(Fin 8 → ℤ)) e
  let r0 := row ⟨0, by decide⟩
  let r1 := row ⟨1, by decide⟩
  let r2 := row ⟨2, by decide⟩
  let r3 := row ⟨3, by decide⟩
  let r4 := row ⟨4, by decide⟩
  let r5 := row ⟨5, by decide⟩
  let r6 := row ⟨6, by decide⟩
  let r7 := row ⟨7, by decide⟩
  logInfo m!"my_simproc row = ![{r0}, {r1}, {r2}, {r3}, {r4}, {r5}, {r6}, {r7}]"
  let z0 : Q(ℤ) := mkIntLit r0
  let z1 : Q(ℤ) := mkIntLit r1
  let z2 : Q(ℤ) := mkIntLit r2
  let z3 : Q(ℤ) := mkIntLit r3
  let z4 : Q(ℤ) := mkIntLit r4
  let z5 : Q(ℤ) := mkIntLit r5
  let z6 : Q(ℤ) := mkIntLit r6
  let z7 : Q(ℤ) := mkIntLit r7
  let result : Q(Fin 8 → ℤ) := q(![$z0, $z1, $z2, $z3, $z4, $z5, $z6, $z7])
  let proof ← mkDecideProof (← mkEq e result)
  return .done { expr := result, proof? := some proof }

private def M₅ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0,  0,  5, -6,  0,  0,  0;
      0,  0,  0,  0,  4, -5,  0,  0;
      0,  0,  0,  0,  0,  3, -4,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

private def M₆ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0,  0,  5, -6,  0,  0,  0;
      0,  0,  0,  0,  4, -5,  0,  0;
      0,  0,  0,  0,  0,  3, -4,  0;
      0,  0,  0,  0,  0,  0,  2, -3;
      0,  0,  0,  0,  0,  0, -1,  2]

private def M₇ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0,  0,  5, -6,  0,  0,  0;
      0,  0,  0,  0,  4, -5,  0,  0;
      0,  0,  0,  0,  0,  3, -4,  0;
      0,  0,  0,  0,  0,  0,  2, -3;
      0,  0,  0,  0,  0,  0,  0,  1]

open Lean Meta in
simproc_decl count_ofNat (Nat.count _ _) := fun e => do
  let some val ← unsafe evalNatExpr e | return .continue
  let result := mkNatLit val
  let proof ← mkDecideProof (← mkEq e result)
  return .done { expr := result, proof? := some proof }

lemma count_201_true_eq_201 : Nat.count (fun _ ↦ True) 201 = 201 := by
  simp only [count_ofNat]




theorem E₈_det : E₈.det = 1 := by
  apply my_helper 2 0 (2:ℤ) (1:ℤ)
  erw [show E₈.updateRow 2 (2 • E₈ 2 + 1 • E₈ 0) = M₁ by decide +kernel]
  apply my_helper 3 1 (2:ℤ) (1:ℤ)
  erw [show M₁.updateRow 3 (2 • M₁ 3 + 1 • M₁ 1) = M₂ by decide +kernel]
  apply my_helper 3 2 (3:ℤ) (2:ℤ)
  erw [show M₂.updateRow 3 (3 • M₂ 3 + 2 • M₂ 2) = M₃ by decide +kernel]
  apply my_helper 4 3 (5:ℤ) (1:ℤ)
  erw [show M₃.updateRow 4 (5 • M₃ 4 + 1 • M₃ 3) = M₄ by decide +kernel]
  apply my_helper 5 4 (4:ℤ) (1:ℤ)
  -- unfold M₄
  simp only [m45_helper]
  erw [show M₄.updateRow 5 (4 • M₄ 5 + 1 • M₄ 4) = M₅ by decide +kernel]
  apply my_helper 6 5 (3:ℤ) (1:ℤ)
  erw [show M₅.updateRow 6 (3 • M₅ 6 + 1 • M₅ 5) = M₆ by decide +kernel]
  apply my_helper 7 6 (2:ℤ) (1:ℤ)
  erw [show M₆.updateRow 7 (2 • M₆ 7 + 1 • M₆ 6) = M₇ by decide +kernel]
  rw [Matrix.det_of_upperTriangular]
  · decide +kernel
  · unfold Matrix.BlockTriangular; decide +kernel
