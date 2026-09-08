import Radix.AST

deriving instance DecidableEq for Except

namespace Radix
mutual
private def tyDecEq : (a b : Ty) → Decidable (a = b)
  | .uint64, b | .bool, b | .unit, b | .string, b => by
    cases b <;> first | exact isTrue rfl | (apply isFalse; intro h; cases h)
  | .array a, b => by
    cases b <;> try (solve | apply isFalse; intro h; cases h)
    rename_i b
    letI := tyDecEq a b
    exact decidable_of_iff (a = b) (by simp)
  | .fn xs a, b => by
    cases b <;> try (solve | apply isFalse; intro h; cases h)
    rename_i ys b
    letI := tysDecEq xs ys
    letI := tyDecEq a b
    exact decidable_of_iff (xs = ys ∧ a = b) (by simp)
termination_by a _ => sizeOf a
private def tysDecEq : (xs ys : List Ty) → Decidable (xs = ys)
  | [], ys => by cases ys <;> first | exact isTrue rfl | (apply isFalse; intro h; cases h)
  | x :: xs, ys => by
    cases ys
    · exact isFalse (by intro h; cases h)
    · rename_i y ys
      letI := tyDecEq x y
      letI := tysDecEq xs ys
      exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
termination_by xs _ => sizeOf xs
end
instance : DecidableEq Ty := tyDecEq
deriving instance DecidableEq for Expr

mutual
private def stmtDecEq : (a other : Stmt) → Decidable (a = other)
  | .skip, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact isTrue rfl
  | .reject, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact isTrue rfl
  | .expectEof, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact isTrue rfl
  | .assign x e, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.assign.injEq _ _ _ _)).symm
  | .readU64 x, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.readU64.injEq _ _)).symm
  | .writeU64 e, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.writeU64.injEq _ _)).symm
  | .writeText x, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.writeText.injEq _ _)).symm
  | .arrSet a i v, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.arrSet.injEq _ _ _ _ _ _)).symm
  | .ret e, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.ret.injEq _ _)).symm
  | .decl x ty e, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.decl.injEq _ _ _ _ _ _)).symm
  | .alloc x ty e, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.alloc.injEq _ _ _ _ _ _)).symm
  | .callStmt x args, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    exact decidable_of_iff _ (Iff.of_eq (Stmt.callStmt.injEq _ _ _ _)).symm
  | .seq a b, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    rename_i a' b'
    letI := stmtDecEq a a'; letI := stmtDecEq b b'
    exact decidable_of_iff _ (Iff.of_eq (Stmt.seq.injEq _ _ _ _)).symm
  | .ite c a b, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    rename_i c' a' b'
    letI := stmtDecEq a a'; letI := stmtDecEq b b'
    exact decidable_of_iff _ (Iff.of_eq (Stmt.ite.injEq _ _ _ _ _ _)).symm
  | .while c b, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    rename_i c' b'
    letI := stmtDecEq b b'
    exact decidable_of_iff _ (Iff.of_eq (Stmt.while.injEq _ _ _ _)).symm
  | .block xs, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    rename_i ys
    letI := stmtsDecEq xs ys
    exact decidable_of_iff _ (Iff.of_eq (Stmt.block.injEq _ _)).symm
  | .scope ps args b, other => by
    cases other <;> try (solve | apply isFalse; intro h; cases h)
    rename_i ps' args' b'
    letI := stmtDecEq b b'
    exact decidable_of_iff _ (Iff.of_eq (Stmt.scope.injEq _ _ _ _ _ _)).symm
termination_by a _ => sizeOf a
private def stmtsDecEq : (xs ys : List Stmt) → Decidable (xs = ys)
  | [], ys => by cases ys <;> first | exact isTrue rfl | (apply isFalse; intro h; cases h)
  | x :: xs, ys => by
    cases ys
    · exact isFalse (by intro h; cases h)
    · rename_i y ys
      letI := stmtDecEq x y; letI := stmtsDecEq xs ys
      exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
termination_by xs _ => sizeOf xs
end
instance : DecidableEq Stmt := stmtDecEq
deriving instance DecidableEq for FunDecl
deriving instance DecidableEq for Program
end Radix
