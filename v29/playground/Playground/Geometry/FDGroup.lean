import Mathlib
import Qq

#check QuaternionGroup

example : 55 ≠ 0 := of_decide_eq_true (Eq.refl true)

#check Lean.Meta.Simp.SimpM

#check Nat.reduceDvd

theorem my_thm (n : ℕ) (h1 : n ≠ 1) (h2 : Odd n) :
    Subgroup.center (DihedralGroup n) = ⊥ := by
  grind [DihedralGroup.center_eq_bot_of_odd_ne_one]

open Qq in
simproc_decl mySimproc' (Subgroup.center (DihedralGroup _)) := fun e => do
  let_expr Subgroup.center g _ ← e | return Lean.Meta.Simp.Step.continue
  let_expr DihedralGroup n ← g | return Lean.Meta.Simp.Step.continue
  let some n' ← Nat.fromExpr? n | return Lean.Meta.Simp.Step.continue
  if n' ≠ 1 ∧ n' % 2 = 1 then
    let neProof ← Lean.Meta.mkDecideProof (← Lean.Meta.mkAppM ``Ne #[n, Lean.mkNatLit 1])
    let oddProof ← Lean.Meta.mkDecideProof (← Lean.Meta.mkAppM ``Odd #[n])
    let result ← Lean.Meta.mkAppM ``my_thm #[n, neProof, oddProof]
    let resultType ← Lean.Meta.inferType result
    let some (_, _, rhs) := resultType.eq? | return .continue
    return .visit {
      expr := rhs,
      proof? := result
    }
  else
    return .continue

#check Set.subset_univ

attribute [grind ←] dvd_iff_exists_eq_mul_left
attribute [grind ←] dvd_of_eq

lemma test'' (n : ℕ) : 2 * n + n ∣ n + n + n := by
  grind

example : Subgroup.center (DihedralGroup 3) = ⊥ := by
  simp only [mySimproc']

example (n : ℕ) : 2 * n = n + n := by
  grind


lemma dvd_iff (a b : ℕ) : (∃ k, b = k * a) ↔ a ∣ b := by
  exact Iff.symm dvd_iff_exists_eq_mul_left

lemma test''' (n : ℕ) : ∃ k, k * n = 99*n + n + n  := by
  grind -lia -ring only

example (n : ℕ) : n ∣ (n + n) := by
  grind


open Lean Meta Mathlib.Tactic Mathlib.Tactic.Ring in
simproc_decl dvdByRingNf (_ ∣ _) := fun e => do
  let_expr Dvd.dvd _ _ a b ← e | return .continue
  try
    -- Create goal: a = b
    let eqType ← mkEq a b
    let mvar ← mkFreshExprMVar eqType
    -- Try to prove a = b using ring
    AtomM.run .reducible (proveEq mvar.mvarId!)
    let eqProof ← instantiateMVars mvar
    -- a = b implies a ∣ b via dvd_of_eq
    let dvdProof ← mkAppM ``dvd_of_eq #[eqProof]
    return .done {
      expr := mkConst ``True
      proof? := some (← mkAppM ``eq_true #[dvdProof])
    }
  catch _ => return .continue

lemma test' (n : ℕ) : 2 * n ∣ n + n := by
  simp only [dvdByRingNf]

@[simp] lemma zmod_two_mul_eq_zero (n : ℕ) : (n : ZMod (2 * n)) + n = 0 := by
  norm_cast
  rw [ZMod.natCast_eq_zero_iff]
  ring_nf
  simp

lemma ndvd_two_then (z : ℕ) (hz : z ∣ 2) : z = 1 ∨ z = 2 := by
  have : z ∈ Nat.divisors 2 := by grind only [= Nat.mem_divisors]
  simp only [Nat.divisors_ofNat] at this
  grind

lemma ndvd_three_then (z : ℕ) (hz : z ∣ 3) : z = 1 ∨ z = 3 := by
  have : z ∈ Nat.divisors 3 := by grind
  simp only [Nat.divisors_ofNat] at this
  grind

lemma three_eq_zero_iff (n : ℕ) : (3 : (ZMod n)) = 0 ↔ n = 1 ∨ n = 3 := by
  constructor
  · intro h
    rw [← @Nat.cast_three (ZMod _), ZMod.natCast_eq_zero_iff] at h
    exact ndvd_three_then _ h
  · rintro (rfl | rfl ) <;> grind

-- Helper: 2 ≠ 0 in ZMod (2*n) when n ≥ 2
private lemma two_ne_zero_zmod (n : ℕ) (h : 2 ≤ n) : (2 : ZMod (2 * n)) ≠ 0 := by
  intro h2
  rw [← @Nat.cast_two (ZMod _), ZMod.natCast_eq_zero_iff] at h2
  linarith [ (Nat.le_of_dvd (by positivity) h2) ]

@[simp] lemma add_left_cancel_iff' {n : ℕ} (a b c : ZMod n) : a + b = a + c ↔ b = c := by
  grind

@[simp] lemma add_left_cancel_iff'' {n : ℕ} (a b c : ZMod n) : a + b = a - c ↔ b = -c := by
  grind
