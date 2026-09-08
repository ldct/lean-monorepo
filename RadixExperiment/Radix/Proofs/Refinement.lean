import Radix.Proofs.Determinism
import Radix.Proofs.InterpCorrectness

namespace Radix

/-- A complete normal fallthrough or ordinary return accepts the entire output. -/
def StmtResult.successful : StmtResult → Prop
  | .normal _ | .returned _ _ => True
  | .rejected _ => False

/-- Successful finite execution from the standard input-dependent initial state.
There is no testing fuel and no problem-specific domain predicate. -/
def RunsSuccessfully (p : Program) (input output : ByteArray) : Prop :=
  ∃ result, BigStep (PState.initFromProgram p input) p.main result ∧
    result.successful ∧ result.state.output = output

/-- Directional exact-output refinement of all accepted reference inputs. -/
def Refines (reference optimized : Program) : Prop :=
  ∀ input output, RunsSuccessfully reference input output →
    RunsSuccessfully optimized input output

theorem Refines.refl (p : Program) : Refines p p := fun _ _ h => h

theorem Refines.trans {p q r : Program} (hpq : Refines p q) (hqr : Refines q r) :
    Refines p r := fun input output h => hqr input output (hpq input output h)

theorem RunsSuccessfully.output_unique {p : Program} {input a b : ByteArray}
    (ha : RunsSuccessfully p input a) (hb : RunsSuccessfully p input b) : a = b := by
  obtain ⟨ra, hra, _, hoa⟩ := ha
  obtain ⟨rb, hrb, _, hob⟩ := hb
  cases BigStep.det hra hrb
  exact hoa.symm.trans hob

theorem RunsSuccessfully.not_rejected {p : Program} {input output : ByteArray}
    (h : RunsSuccessfully p input output)
    (hr : BigStep (PState.initFromProgram p input) p.main (.rejected σ)) : False := by
  obtain ⟨r, hrun, hs, _⟩ := h
  cases BigStep.det hrun hr
  exact hs

theorem reject_never_succeeds (funs : List FunDecl) (input output : ByteArray) :
    ¬ RunsSuccessfully ⟨funs, .reject⟩ input output := by
  intro h
  exact h.not_rejected BigStep.reject

theorem reject_refines (funs : List FunDecl) (p : Program) :
    Refines ⟨funs, .reject⟩ p := by
  intro input output h
  exact False.elim (reject_never_succeeds funs input output h)

/-- A successful interpreter test is evidence for the fuel-free execution API. -/
theorem Program.run_successful {p : Program} {input : ByteArray} {fuel : Nat}
    {σ : PState} (h : p.run fuel input = .ok σ) : RunsSuccessfully p input σ.output := by
  unfold Program.run at h
  simp only [] at h
  split at h
  · rename_i rv σ' he
    simp only [Except.ok.injEq] at h
    subst σ'
    refine ⟨toStmtResult rv σ, Stmt.interp_sound he, ?_, ?_⟩
    · cases rv <;> trivial
    · cases rv <;> rfl
  · simp at h

end Radix
