import Radix.Linear

/-! # Linear Ownership Typing Tests

Positive examples show typing derivations go through.
Negative examples show certain programs are untypeable.
-/

namespace Radix.Tests.Linear
open Std

/-! ## Positive examples -/

/-- Skip preserves any ownership. -/
example : LinearOk ∅ .skip ∅ := LinearOk.skip

/-- Assignment to a non-owned variable. -/
example : LinearOk ∅ (.assign "x" (Expr.lit (.uint64 1))) ∅ :=
  LinearOk.assign HashSet.not_mem_empty

/-- Alloc produces ownership. -/
example : LinearOk ∅
    (Stmt.alloc "arr" .uint64 (Expr.lit (.uint64 3)))
    ((∅ : Owned).insert "arr") :=
  LinearOk.alloc HashSet.not_mem_empty

/-- Alloc → write → free: complete lifecycle.
    Output is `(∅.insert "arr").erase "arr"`, which has no members. -/
def allocWriteFree : LinearOk ∅ (
  Stmt.alloc "arr" .uint64 (Expr.lit (.uint64 3)) ;;
  Stmt.arrSet (Expr.var "arr") (Expr.lit (.uint64 0)) (Expr.lit (.uint64 42)) ;;
  Stmt.free (Expr.var "arr")
) (((∅ : Owned).insert "arr").erase "arr") :=
  LinearOk.seq (LinearOk.alloc HashSet.not_mem_empty)
    (LinearOk.seq (LinearOk.arrSet (HashSet.mem_insert_self ..))
      (LinearOk.free (HashSet.mem_insert_self ..)))

/-- The output of alloc-write-free has no owned variables. -/
example : ∀ x, x ∉ (((∅ : Owned).insert "arr").erase "arr") := by
  intro x; simp [HashSet.mem_erase]

/-- If-then-else with balanced ownership in both branches. -/
def iteBalanced : LinearOk ((∅ : Owned).insert "arr") (
  Stmt.ite (Expr.lit (.bool true))
    (Stmt.free (Expr.var "arr"))
    (Stmt.free (Expr.var "arr"))
) (((∅ : Owned).insert "arr").erase "arr") :=
  LinearOk.ite
    (LinearOk.free (HashSet.mem_insert_self ..))
    (LinearOk.free (HashSet.mem_insert_self ..))

/-- While loop preserves ownership (body must be balanced). -/
example : LinearOk ∅ (Stmt.while (Expr.lit (.bool true)) .skip) ∅ :=
  LinearOk.whileLoop LinearOk.skip

/-- Return preserves ownership. -/
example : LinearOk ∅ (Stmt.ret (Expr.lit (.uint64 0))) ∅ :=
  LinearOk.ret

/-! ## Negative examples -/

/-- Double free is not typeable: after free, "arr" is no longer owned.
    We generalize over `O'` to avoid dependent elimination issues. -/
example : ¬ ∃ O', LinearOk ∅ (
  Stmt.alloc "arr" .uint64 (Expr.lit (.uint64 1)) ;;
  Stmt.free (Expr.var "arr") ;;
  Stmt.free (Expr.var "arr")
) O' := by
  intro ⟨O', h⟩
  cases h with | seq ha h2 =>
  cases ha
  cases h2 with | seq hf1 hf2 =>
  cases hf1 with | free hx =>
  cases hf2 with | free hx2 =>
  simp [HashSet.mem_erase, HashSet.mem_insert] at hx2

/-- Leak: alloc without free doesn't reach ∅. -/
example : ¬ ∃ O', LinearOk ∅
    (Stmt.alloc "arr" .uint64 (Expr.lit (.uint64 1))) O' ∧ ∀ x, x ∉ O' := by
  intro ⟨O', h, hempty⟩
  cases h with | alloc _ =>
  exact absurd (HashSet.mem_insert_self ..) (hempty "arr")

/-- Overwriting an owned variable is disallowed (would leak). -/
example : ¬ ∃ O', LinearOk ((∅ : Owned).insert "x")
    (.assign "x" (Expr.lit (.uint64 0))) O' := by
  intro ⟨O', h⟩
  cases h with | assign hx =>
  exact absurd (HashSet.mem_insert_self ..) hx

end Radix.Tests.Linear
