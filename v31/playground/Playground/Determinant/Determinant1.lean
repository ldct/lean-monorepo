import Mathlib

namespace Determinant1

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
unsafe def evalNatExpr (e : Expr) : MetaM (Option Nat) := do
  let ty ← inferType e
  let .const ``Nat _ := ty | return none
  let val ← Lean.Meta.evalExpr Nat (mkConst ``Nat) e
  return some val

open Lean Meta in
simproc_decl count_ofNat (Nat.count _ _) := fun e => do
  let some val ← unsafe evalNatExpr e | return .continue
  let result := mkNatLit val
  let proof ← mkDecideProof (← mkEq e result)
  return .done { expr := result, proof? := some proof }

lemma count_201_true_eq_201 : Nat.count (fun _ ↦ True) 201 = 201 := by
  simp only [count_ofNat]

open Lean Meta in
unsafe def evalIntExpr (e : Expr) : MetaM (Option Int) := do
  let ty ← inferType e
  let .const ``Int _ := ty | return none
  let val ← Lean.Meta.evalExpr Int (mkConst ``Int) e
  return some val

open Lean Meta in
simproc_decl eval_M₄_entry (M₄ _ _) := fun e => do
  let some val ← unsafe evalIntExpr e | return .continue
  let result := Lean.mkIntLit val
  let proof ← mkDecideProof (← mkEq e result)
  return .done { expr := result, proof? := some proof }

lemma m45_helper : M₄ 5 = ![0, 0, 0, 0, -1, 2, -1, 0] := by
  funext i
  fin_cases i <;> simp [eval_M₄_entry]

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

end Determinant1
