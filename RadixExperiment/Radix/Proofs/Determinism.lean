/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt

/-! # Determinism of Big-Step Semantics

Proof that the big-step semantics is deterministic: if a statement evaluates
to two results from the same state, those results must be equal.

This is a foundational property -- it means the optimization correctness
theorems (`constFold_correct`, `deadCodeElim_correct`, etc.) actually imply
observational equivalence, not just that the optimized program is one
possible behavior.

The proof uses `grind` for cases that reduce to equational contradictions
or functional injectivity (e.g., `some true = some false` is absurd),
and explicit inductive hypothesis application for recursive cases
(`seq`, `while`, `call`).
-/

namespace Radix

/-- The big-step semantics is deterministic: same state + same statement
implies same result. -/
theorem BigStep.det (h₁ : BigStep σ s r₁) (h₂ : BigStep σ s r₂) : r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | skip => cases h₂; rfl
  | assign he₁ hs₁ => cases h₂ with | assign => grind
  | decl he₁ hs₁ => cases h₂ with | decl => grind
  | ifTrue hc₁ ht₁ iht => cases h₂ with
    | ifTrue _ ht₂ => exact iht ht₂
    | ifFalse hc₂ _ => grind
  | ifFalse hc₁ hf₁ ihf => cases h₂ with
    | ifTrue hc₂ _ => grind
    | ifFalse _ hf₂ => exact ihf hf₂
  | whileFalse hc₁ => cases h₂ with
    | whileTrue hc₂ _ _ => grind
    | whileReturn hc₂ _ => grind
    | whileFalse _ => rfl
  | alloc hsz₁ ha₁ hs₁ => cases h₂ with | alloc => grind
  | free he₁ hf₁ => cases h₂ with | free => grind
  | arrSet harr₁ hidx₁ hval₁ hw₁ => cases h₂ with | arrSet => grind
  | ret he₁ => cases h₂ with | ret => grind
  | block _ ihb => cases h₂ with | block hb₂ => exact ihb hb₂
  | seqNormal hs₁ hs₂ ih₁ ih₂ =>
    cases h₂ with
    | seqNormal hs₁' hs₂' => cases ih₁ hs₁'; exact ih₂ hs₂'
    | seqReturn hs₁' => cases ih₁ hs₁'
  | seqReturn hs₁ ih₁ =>
    cases h₂ with
    | seqNormal hs₁' _ => cases ih₁ hs₁'
    | seqReturn hs₁' => exact ih₁ hs₁'
  | whileTrue hc hb hw ihb ihw =>
    cases h₂ with
    | whileTrue _ hb₂ hw₂ => cases ihb hb₂; exact ihw hw₂
    | whileReturn _ hb₂ => cases ihb hb₂
    | whileFalse hc₂ => grind
  | whileReturn hc hb ihb =>
    cases h₂ with
    | whileTrue _ hb₂ _ => cases ihb hb₂
    | whileReturn _ hb₂ => exact ihb hb₂
    | whileFalse hc₂ => grind
  | callStmt hlook hargs hparams hframe hbody hpop ihbody =>
    cases h₂ with
    | callStmt hlook₂ hargs₂ hparams₂ hframe₂ hbody₂ hpop₂ =>
      simp_all [PState.lookupFun]
      cases ihbody hbody₂
      simp_all
  | scope hargs hlen hframe hbody hpop ihbody =>
    cases h₂ with
    | scope hargs₂ hlen₂ hframe₂ hbody₂ hpop₂ =>
      simp_all
      cases ihbody hbody₂
      simp_all

end Radix
