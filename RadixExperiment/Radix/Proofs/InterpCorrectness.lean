/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Interp
import Radix.Eval.Stmt

/-! # Interpreter Correctness

Proofs that the fuel-based interpreter (`Stmt.interp`) is correct with respect
to the relational big-step semantics (`BigStep`).

## Main results

- `Stmt.interp_fuel_mono`: fuel monotonicity — if `interp` succeeds with fuel
  `n`, it succeeds with the same result with any `m ≥ n`.
- `Stmt.interp_complete`: completeness — if `BigStep σ s r`, there exists enough
  fuel for `interp` to produce the same result.
- `Stmt.interp_sound`: soundness — if `interp` succeeds, then `BigStep` holds
  for the corresponding result.
-/

namespace Radix

/-! ## Helper definitions and lemmas -/

/-- Extract the optional return value from a statement result. -/
@[simp] def StmtResult.retVal : StmtResult → Option Value
  | .normal _ => none
  | .returned v _ => some v
  | .rejected _ => none

@[simp] def StmtResult.outcome : StmtResult → Except InterpError (Option Value)
  | .normal _ => .ok none
  | .returned v _ => .ok (some v)
  | .rejected _ => .error .rejected

@[simp] theorem evalExpr_ok {e : Expr} {σ : PState} {v : Value}
    (h : e.eval σ = some v) : evalExpr e σ = .ok v := by
  simp [evalExpr, h]

private theorem evalArgs_aux {args : List Expr} {σ : PState} {vs : List Value}
    (h : args.mapM (Expr.eval σ) = some vs) :
    args.mapM (fun e => evalExpr e σ) = .ok vs := by
  induction args generalizing vs with
  | nil =>
    simp only [List.mapM_nil] at h
    change some [] = some vs at h
    obtain rfl := Option.some.inj h
    rfl
  | cons a as ih =>
    simp only [List.mapM_cons] at h
    change Option.bind (a.eval σ) (fun v =>
      Option.bind (as.mapM (Expr.eval σ)) (fun vs' => some (v :: vs'))) = some vs at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h₂⟩ := h
    rw [Option.bind_eq_some_iff] at h₂
    obtain ⟨vs', hvs', h₃⟩ := h₂
    obtain rfl := Option.some.inj h₃
    rw [List.mapM_cons]
    simp [evalExpr_ok hv, ih hvs', bind, Except.bind, pure, Except.pure]

theorem evalArgs_ok {args : List Expr} {σ : PState} {vs : List Value}
    (h : args.mapM (Expr.eval σ) = some vs) : evalArgs args σ = .ok vs := by
  simp [evalArgs]
  exact evalArgs_aux h

theorem mkFrame_ok {params : List (String × Ty)} {vs : List Value} {frame : Frame}
    (hlen : params.length = vs.length)
    (hframe : frame = { env := (params.zip vs).foldl (fun env (p, v) => env.set p.1 v) Env.empty }) :
    mkFrame params vs = .ok frame := by
  unfold mkFrame
  simp only [ne_eq, bind, Except.bind, pure, Except.pure]
  split
  · next h => omega
  · exact congrArg Except.ok hframe.symm

@[simp] theorem andThen_ok_none {σ' : PState} {k : PState → InterpResult} :
    andThen (.ok none, σ') k = k σ' := rfl

@[simp] theorem andThen_ok_some {v : Value} {σ' : PState} {k : PState → InterpResult} :
    andThen (.ok (some v), σ') k = (.ok (some v), σ') := rfl

@[simp] theorem andThen_error {e : InterpError} {σ' : PState} {k : PState → InterpResult} :
    andThen (.error e, σ') k = (.error e, σ') := rfl

@[simp] theorem evalExpr_ok' {e : Expr} {σ : PState} {v : Value}
    (h : evalExpr e σ = .ok v) : e.eval σ = some v := by
  simp [evalExpr] at h
  split at h <;> simp_all

private theorem evalArgs_aux' {args : List Expr} {σ : PState} {vs : List Value}
    (h : args.mapM (fun e => evalExpr e σ) = .ok vs) :
    args.mapM (Expr.eval σ) = some vs := by
  induction args generalizing vs with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | cons a as ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v hv
      split at h
      · simp at h
      · rename_i vs' hvs'
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [List.mapM_cons]
        simp [evalExpr_ok' hv, ih hvs', ← h]

theorem evalArgs_ok' {args : List Expr} {σ : PState} {vs : List Value}
    (h : evalArgs args σ = .ok vs) : args.mapM (Expr.eval σ) = some vs := by
  simp [evalArgs] at h
  exact evalArgs_aux' h

theorem mkFrame_ok' {params : List (String × Ty)} {vs : List Value} {frame : Frame}
    (h : mkFrame params vs = .ok frame) :
    params.length = vs.length ∧
    frame = { env := (params.zip vs).foldl (fun env (p, v) => env.set p.1 v) Env.empty } := by
  unfold mkFrame at h
  simp only [ne_eq, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i hlen
    simp only [Except.ok.injEq] at h
    constructor
    · omega
    · subst h; rfl

/-! ## Fuel monotonicity -/

 theorem Stmt.interp_mono {n m : Nat} (hle : n ≤ m)
    {s : Stmt} {σ σ' : PState} {out : Except InterpError (Option Value)}
    (hterm : out ≠ .error .fuelExhausted)
    (h : s.interp n σ = (out, σ')) : s.interp m σ = (out, σ') := by
  induction n generalizing m s σ σ' out with
  | zero => simp [Stmt.interp] at h; grind
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
    simp only [Nat.succ_add]
    have ih := @ih (n + m) (Nat.le_add_right n m)
    cases s <;> simp only [Stmt.interp] at h ⊢
    all_goals
      try simp only [andThen] at h ⊢
      repeat' (split at h <;> (try simp_all))
      all_goals try simp_all
      all_goals try
        have hm := ih (out := .error .rejected) (by simp) (by assumption)
        simp_all
      all_goals grind only


theorem Stmt.interp_fuel_mono {n m : Nat} (hle : n ≤ m)
    {s : Stmt} {σ σ' : PState} {rv : Option Value}
    (h : s.interp n σ = (.ok rv, σ')) : s.interp m σ = (.ok rv, σ') :=
  interp_mono hle (by simp) h

@[simp] theorem StmtResult.outcome_not_fuel (r : StmtResult) :
    r.outcome ≠ .error .fuelExhausted := by cases r <;> simp

/-! ## Completeness -/

/-- If `BigStep σ s r`, there exists enough fuel for `interp` to produce the
corresponding result. -/
theorem Stmt.interp_complete
    {σ : PState} {s : Stmt} {r : StmtResult}
    (h : BigStep σ s r) :
    ∃ fuel : Nat, s.interp fuel σ = (r.outcome, r.state) := by
  induction h with
  | skip =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state]

  | assign he hs =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state, evalExpr, he, hs]

  | decl he hs =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state, evalExpr, he, hs]

  | seqNormal h₁ h₂ ih₁ ih₂ =>
    obtain ⟨n₁, hn₁⟩ := ih₁
    obtain ⟨n₂, hn₂⟩ := ih₂
    simp only [StmtResult.outcome, StmtResult.state] at hn₁
    refine ⟨max n₁ n₂ + 1, ?_⟩
    unfold Stmt.interp; simp only [andThen]
    rw [interp_mono (Nat.le_max_left n₁ n₂) (by simp) hn₁]
    exact interp_mono (Nat.le_max_right n₁ n₂) (StmtResult.outcome_not_fuel _) hn₂

  | seqReturn h₁ ih₁ =>
    obtain ⟨n₁, hn₁⟩ := ih₁
    simp only [StmtResult.outcome, StmtResult.state] at hn₁ ⊢
    refine ⟨n₁ + 1, ?_⟩
    unfold Stmt.interp; simp only [andThen]
    rw [interp_fuel_mono (Nat.le_refl n₁) hn₁]

  | ifTrue hc ht iht =>
    obtain ⟨n, hn⟩ := iht
    refine ⟨n + 1, ?_⟩
    unfold Stmt.interp
    simp [evalExpr, hc, hn]

  | ifFalse hc hf ihf =>
    obtain ⟨n, hn⟩ := ihf
    refine ⟨n + 1, ?_⟩
    unfold Stmt.interp
    simp [evalExpr, hc, hn]

  | whileTrue hc hb hw ihb ihw =>
    obtain ⟨nb, hnb⟩ := ihb
    obtain ⟨nw, hnw⟩ := ihw
    simp only [StmtResult.outcome, StmtResult.state] at hnb
    refine ⟨max nb nw + 1, ?_⟩
    unfold Stmt.interp
    simp only [evalExpr, hc, andThen]
    rw [interp_fuel_mono (Nat.le_max_left nb nw) hnb]
    exact interp_mono (Nat.le_max_right nb nw) (StmtResult.outcome_not_fuel _) hnw

  | whileReturn hc hb ihb =>
    obtain ⟨nb, hnb⟩ := ihb
    simp only [StmtResult.outcome, StmtResult.state] at hnb ⊢
    refine ⟨nb + 1, ?_⟩
    unfold Stmt.interp
    simp only [evalExpr, hc, andThen]
    rw [interp_fuel_mono (Nat.le_refl nb) hnb]

  | whileFalse hc =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state, evalExpr, hc]

  | alloc hsz ha hs =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state, evalExpr, hsz, ha, hs]

  | reject => exact ⟨1, by simp [Stmt.interp, StmtResult.state]⟩
  | readU64 hr hs =>
    exact ⟨1, by simp [Stmt.interp, hr, hs, StmtResult.state]⟩
  | readReject hr =>
    exact ⟨1, by simp [Stmt.interp, hr, StmtResult.state]⟩
  | writeU64 he =>
    exact ⟨1, by simp [Stmt.interp, evalExpr, he, StmtResult.state]⟩
  | writeText => exact ⟨1, by simp [Stmt.interp, StmtResult.state]⟩
  | expectEof he => exact ⟨1, by simp [Stmt.interp, he, StmtResult.state]⟩
  | eofReject he => exact ⟨1, by simp [Stmt.interp, he, StmtResult.state]⟩
  | seqReject h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [Stmt.interp, hn, andThen, StmtResult.state]⟩
  | whileReject hc h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [Stmt.interp, evalExpr, hc, hn, andThen, StmtResult.state]⟩

  | arrSet harr hidx hval hw =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state, evalExpr, harr, hidx, hval, hw]

  | ret he =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.outcome, StmtResult.state, evalExpr, he]

  | block hb ihb =>
    obtain ⟨n, hn⟩ := ihb
    exact ⟨n + 1, by unfold Stmt.interp; exact hn⟩

  | @callStmt fd vs frame bodyResult fr σ' σ name args hlook hargs hparams hframe hbody hpop ihbody =>
    obtain ⟨nb, hnb⟩ := ihbody
    refine ⟨nb + 1, ?_⟩
    unfold Stmt.interp; simp only [hlook, evalArgs_ok hargs, mkFrame_ok hparams hframe]
    rw [hnb]
    cases bodyResult <;> simp_all [StmtResult.state, StmtResult.afterCall]

  | @scope vs frame body bodyResult fr σ' σ params args hargs hlen hframe hbody hpop ihbody =>
    obtain ⟨nb, hnb⟩ := ihbody
    refine ⟨nb + 1, ?_⟩
    unfold Stmt.interp; simp only [evalArgs_ok hargs, mkFrame_ok hlen hframe]
    rw [hnb]
    cases bodyResult <;> simp_all [StmtResult.state, StmtResult.afterCall]


/-! ## Soundness -/

/-- Convert an interpreter result to a `StmtResult`. -/
@[simp] def toStmtResult (rv : Option Value) (σ' : PState) : StmtResult :=
  match rv with | none => .normal σ' | some v => .returned v σ'

@[simp] theorem toStmtResult_state (rv : Option Value) (σ : PState) :
    (toStmtResult rv σ).state = σ := by
  cases rv <;> rfl

/-- If the interpreter succeeds, the big-step relation holds. -/
theorem Stmt.interp_sound {fuel : Nat} {s : Stmt} {σ σ' : PState} {rv : Option Value}
    (h : s.interp fuel σ = (.ok rv, σ')) :
    BigStep σ s (toStmtResult rv σ') := by
  induction fuel generalizing s σ σ' rv with
  | zero => simp [Stmt.interp] at h
  | succ n ih =>
    unfold Stmt.interp at h
    match s with
    | .skip =>
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .skip
    | .assign x e =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i v hv
        split at h
        · rename_i σ₂ hs
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact .assign (evalExpr_ok' hv) hs
        · simp at h
    | .decl x _ty e =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i v hv
        split at h
        · rename_i σ₂ hs
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact .decl (evalExpr_ok' hv) hs
        · simp at h
    | .seq s₁ s₂ =>
      simp only [andThen] at h
      split at h
      · rename_i σ₂ h₁
        exact .seqNormal (ih h₁) (ih h)
      · rename_i v σ₂ h₁
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact .seqReturn (ih h₁)
      · simp at h
    | .ite c t f =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i hc
        exact .ifTrue (evalExpr_ok' hc) (ih h)
      · rename_i hc
        exact .ifFalse (evalExpr_ok' hc) (ih h)
      · simp at h
    | .while c b =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i hc
        simp only [andThen] at h
        split at h
        · rename_i σ₂ hb
          exact .whileTrue (evalExpr_ok' hc) (ih hb) (ih h)
        · rename_i v σ₂ hb
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact .whileReturn (evalExpr_ok' hc) (ih hb)
        · simp at h
      · rename_i hc
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact .whileFalse (evalExpr_ok' hc)
      · simp at h
    | .alloc x _ty szExpr =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i sz hsz
        split at h
        · rename_i σ₂ hs
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact .alloc (evalExpr_ok' hsz) rfl hs
        · simp at h
      · simp at h
    | .reject => simp at h
    | .readU64 x =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i n hr
        split at h
        · rename_i σ₂ hs
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact .readU64 (by cases hh : ByteIO.readU64 σ.input σ.cursor; simp_all) hs
        · simp at h
    | .writeU64 e =>
      simp only [] at h
      split at h
      · rename_i n he
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact .writeU64 (evalExpr_ok' he)
      · simp at h
    | .writeText text =>
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .writeText
    | .expectEof =>
      simp only [] at h
      split at h
      · rename_i he
        simp at h; obtain ⟨rfl, rfl⟩ := h
        simpa [he] using (BigStep.expectEof (σ := σ) he)
      · simp at h
    | .arrSet arr idx val =>
      simp only [] at h
      split at h <;> (try simp at h)
      rename_i a i vv harr hidx hval
      split at h
      · rename_i heap' hw
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact .arrSet (evalExpr_ok' harr) (evalExpr_ok' hidx) (evalExpr_ok' hval) hw
      · simp at h
    | .ret e =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i v he
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact .ret (evalExpr_ok' he)
    | .block stmts =>
      exact .block (ih h)
    | .callStmt name args =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i fd hlook
        split at h
        · simp at h
        · rename_i vs hargs
          split at h
          · simp at h
          · rename_i frame hmk
            obtain ⟨hlen, hframe⟩ := mkFrame_ok' hmk
            match hbody : Stmt.interp n fd.body (σ.pushFrame frame) with
            | (.error msg, σ₂) =>
              rw [hbody] at h; simp only [] at h; split at h <;> simp_all
            | (.ok rv₂, σ₂) =>
              rw [hbody] at h
              match hpop : σ₂.popFrame with
              | some (fr, σ₃) =>
                simp [hpop] at h; obtain ⟨rfl, rfl⟩ := h
                have hpop' : (toStmtResult rv₂ σ₂).state.popFrame = some (fr, σ₃) := by
                  cases rv₂ <;> exact hpop
                have hb := BigStep.callStmt hlook (evalArgs_ok' hargs) hlen hframe (ih hbody) hpop'
                cases rv₂ <;> exact hb
              | none =>
                simp [hpop] at h
    | .scope params args body =>
      simp only [] at h
      split at h
      · simp at h
      · rename_i vs hargs
        split at h
        · simp at h
        · rename_i frame hmk
          obtain ⟨hlen, hframe⟩ := mkFrame_ok' hmk
          match hbody : Stmt.interp n body (σ.pushFrame frame) with
          | (.error msg, σ₂) =>
            rw [hbody] at h; simp only [] at h; split at h <;> simp_all
          | (.ok rv₂, σ₂) =>
            rw [hbody] at h
            match hpop : σ₂.popFrame with
            | some (fr, σ₃) =>
              simp [hpop] at h; obtain ⟨rfl, rfl⟩ := h
              have hpop' : (toStmtResult rv₂ σ₂).state.popFrame = some (fr, σ₃) := by
                cases rv₂ <;> exact hpop
              have hb := BigStep.scope (evalArgs_ok' hargs) hlen hframe (ih hbody) hpop'
              cases rv₂ <;> exact hb
            | none =>
              simp [hpop] at h


end Radix
