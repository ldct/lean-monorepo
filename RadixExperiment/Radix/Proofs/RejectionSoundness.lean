import Radix.Proofs.InterpCorrectness

namespace Radix

private theorem evalExpr_not_rejected (e : Expr) (σ : PState) :
    evalExpr e σ ≠ .error .rejected := by
  simp [evalExpr]; split <;> simp_all

private theorem evalArgs_not_rejected (args : List Expr) (σ : PState) :
    evalArgs args σ ≠ .error .rejected := by
  induction args with
  | nil => simp [evalArgs, List.mapM_nil, pure, Except.pure]
  | cons a as ih =>
    simp only [evalArgs, List.mapM_cons, bind, Except.bind]
    cases he : evalExpr a σ with
    | error e =>
      have h := evalExpr_not_rejected a σ
      simp_all
    | ok v =>
      simp only [pure, Except.pure]
      cases he : as.mapM (fun e => evalExpr e σ) <;> simp_all [evalArgs]


private theorem mkFrame_not_rejected (params : List (String × Ty)) (vs : List Value) :
    mkFrame params vs ≠ .error .rejected := by
  simp [mkFrame, bind, Except.bind, pure, Except.pure]
  split <;> simp_all

/-- Rejection reported by the interpreter has a finite relational derivation;
it cannot be confused with a runtime fault or exhausted testing fuel. -/
theorem Stmt.interp_rejected_sound {fuel : Nat} {s : Stmt} {σ σ' : PState}
    (h : s.interp fuel σ = (.error .rejected, σ')) :
    BigStep σ s (.rejected σ') := by
  induction fuel generalizing s σ σ' with
  | zero => simp [Stmt.interp] at h
  | succ n ih =>
    cases s with
    | skip | writeText => simp [Stmt.interp] at h
    | assign x e | decl x ty e | ret e | alloc x ty e | writeU64 e =>
      have hn := evalExpr_not_rejected e σ
      simp only [Stmt.interp] at h
      repeat' split at h
      all_goals simp_all
    | arrSet arr idx val =>
      have ha := evalExpr_not_rejected arr σ
      have hi := evalExpr_not_rejected idx σ
      have hv := evalExpr_not_rejected val σ
      simp only [Stmt.interp] at h
      repeat' split at h
      all_goals simp_all
    | reject =>
      simp only [Stmt.interp, Prod.mk.injEq, true_and] at h
      subst σ'; exact .reject
    | readU64 x =>
      simp only [Stmt.interp] at h
      split at h
      · rename_i hr
        simp only [Prod.mk.injEq, true_and] at h
        subst σ'
        exact .readReject (by cases hh : ByteIO.readU64 σ.input σ.cursor; simp_all)
      · split at h <;> simp_all
    | expectEof =>
      simp only [Stmt.interp] at h
      split at h
      · simp at h
      · rename_i he
        simp only [Prod.mk.injEq, true_and] at h
        subst σ'; exact .eofReject he
    | seq s₁ s₂ =>
      simp only [Stmt.interp, andThen] at h
      split at h
      · rename_i σ₂ h₁
        exact .seqNormal (Stmt.interp_sound h₁) (ih h)
      · simp at h
      · rename_i err σ₂ h₁
        simp only [Prod.mk.injEq, Except.error.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .seqReject (ih h₁)
    | ite c t f =>
      simp only [Stmt.interp] at h
      split at h
      · rename_i err he
        have := evalExpr_not_rejected c σ
        simp_all
      · rename_i he
        exact .ifTrue (evalExpr_ok' he) (ih h)
      · rename_i he
        exact .ifFalse (evalExpr_ok' he) (ih h)
      · simp at h
    | «while» c b =>
      simp only [Stmt.interp] at h
      split at h
      · rename_i err he
        have := evalExpr_not_rejected c σ
        simp_all
      · rename_i hc
        simp only [andThen] at h
        split at h
        · rename_i σ₂ hb
          exact .whileTrue (evalExpr_ok' hc) (Stmt.interp_sound hb) (ih h)
        · simp at h
        · rename_i err σ₂ hb
          simp only [Prod.mk.injEq, Except.error.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .whileReject (evalExpr_ok' hc) (ih hb)
      · simp at h
      · simp at h
    | block ss => exact .block (ih (by simpa only [Stmt.interp] using h))
    | callStmt name args =>
      simp only [Stmt.interp] at h
      split at h
      · simp at h
      · rename_i fd hlook
        split at h
        · have := evalArgs_not_rejected args σ; simp_all
        · rename_i vs hargs
          split at h
          · have := mkFrame_not_rejected fd.params vs; simp_all
          · rename_i frame hmk
            obtain ⟨hlen, hframe⟩ := mkFrame_ok' hmk
            match hbody : Stmt.interp n fd.body (σ.pushFrame frame) with
            | (.error msg, σ₂) =>
              rw [hbody] at h
              match hpop : σ₂.popFrame with
              | some (fr, σ₃) =>
                simp [hpop] at h; obtain ⟨rfl, rfl⟩ := h
                exact .callStmt hlook (evalArgs_ok' hargs) hlen hframe (ih hbody) hpop
              | none => simp [hpop] at h; split at h <;> simp_all
            | (.ok rv, σ₂) =>
              rw [hbody] at h; simp only [] at h; split at h <;> simp_all
    | scope params args body =>
      simp only [Stmt.interp] at h
      split at h
      · have := evalArgs_not_rejected args σ; simp_all
      · rename_i vs hargs
        split at h
        · have := mkFrame_not_rejected params vs; simp_all
        · rename_i frame hmk
          obtain ⟨hlen, hframe⟩ := mkFrame_ok' hmk
          match hbody : Stmt.interp n body (σ.pushFrame frame) with
          | (.error msg, σ₂) =>
            rw [hbody] at h
            match hpop : σ₂.popFrame with
            | some (fr, σ₃) =>
              simp [hpop] at h; obtain ⟨rfl, rfl⟩ := h
              exact .scope (evalArgs_ok' hargs) hlen hframe (ih hbody) hpop
            | none => simp [hpop] at h; split at h <;> simp_all
          | (.ok rv, σ₂) =>
            rw [hbody] at h; simp only [] at h; split at h <;> simp_all


/-- Soundness covers every relational outcome, including explicit rejection. -/
theorem Stmt.interp_result_sound {fuel : Nat} {s : Stmt} {σ : PState} {r : StmtResult}
    (h : s.interp fuel σ = (r.outcome, r.state)) : BigStep σ s r := by
  cases r with
  | normal σ' => exact Stmt.interp_sound h
  | returned v σ' => exact Stmt.interp_sound h
  | rejected σ' => exact Stmt.interp_rejected_sound h

/-- The fuel-free relation agrees exactly with complete interpreter outcomes. -/
theorem Stmt.interp_iff_bigStep {s : Stmt} {σ : PState} {r : StmtResult} :
    BigStep σ s r ↔ ∃ fuel, s.interp fuel σ = (r.outcome, r.state) := by
  constructor
  · exact Stmt.interp_complete
  · rintro ⟨fuel, h⟩; exact Stmt.interp_result_sound h

end Radix
