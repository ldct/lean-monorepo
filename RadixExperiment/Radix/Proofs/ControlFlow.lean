import Radix.Proofs.Refinement
import Radix.Proofs.Hoare

namespace Radix

mutual
/-- Syntactic returns that can escape the current statement. A call consumes
ordinary returns from its body, while rejection remains a separate outcome. -/
def Stmt.mayReturn : Stmt → Bool
  | .ret _ => true
  | .seq a b => a.mayReturn || b.mayReturn
  | .ite _ a b => a.mayReturn || b.mayReturn
  | .while _ b => b.mayReturn
  | .block ss => Stmt.listMayReturn ss
  | _ => false

def Stmt.listMayReturn : List Stmt → Bool
  | [] => false
  | s :: ss => s.mayReturn || Stmt.listMayReturn ss
end

theorem Stmt.fold_mayReturn (ss : List Stmt) (init : Stmt) :
    (ss.foldl (· ;; ·) init).mayReturn = (init.mayReturn || Stmt.listMayReturn ss) := by
  induction ss generalizing init with
  | nil => simp [Stmt.listMayReturn]
  | cons s ss ih => simp [List.foldl, ih, Stmt.mayReturn, Stmt.listMayReturn, Bool.or_assoc]

/-- A checked statement with no escaping return cannot produce one. -/
theorem BigStep.return_requires_ret (h : BigStep σ s (.returned v σ')) :
    s.mayReturn = true := by
  generalize hr : StmtResult.returned v σ' = r at h
  induction h generalizing v σ' with
  | seqNormal h1 h2 ih1 ih2 => simp [Stmt.mayReturn, ih2 hr]
  | seqReturn h ih => simp [Stmt.mayReturn, ih rfl]
  | ifTrue hc h ih => simp [Stmt.mayReturn, ih hr]
  | ifFalse hc h ih => simp [Stmt.mayReturn, ih hr]
  | whileTrue hc hb hw ihb ihw => exact ihw hr
  | whileReturn hc hb ih => exact ih rfl
  | ret => rfl
  | block h ih =>
    have hh := ih hr
    simpa [Stmt.fold_mayReturn, Stmt.mayReturn] using hh
  | @callStmt fd vs frame result fr st st0 name args _ _ _ _ _ _ _ =>
    cases result <;> cases hr
  | @scope vs frame body result fr st st0 params args _ _ _ _ _ _ =>
    cases result <;> cases hr
  | _ => cases hr

/-- For return-free programs, successful completion is precisely normal completion. -/
theorem RunsSuccessfully.normal {p : Program} (hp : p.main.mayReturn = false)
    (h : RunsSuccessfully p input output) :
    ∃ σ, BigStep (PState.initFromProgram p input) p.main (.normal σ) ∧ σ.output = output := by
  obtain ⟨r, hr, hs, hout⟩ := h
  cases r with
  | normal σ => exact ⟨σ, hr, hout⟩
  | returned v σ => have := hr.return_requires_ret; simp [hp] at this
  | rejected σ => exact False.elim hs

end Radix
