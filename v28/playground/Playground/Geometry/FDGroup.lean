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

#check DihedralGroup.center_eq_bot_of_odd_ne_one

open DihedralGroup in
def halfTurnClosure (n : ℕ) : Subgroup (DihedralGroup (2*n)) where
  carrier := { 1, r n }
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  one_mem' := by grind
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
    rcases ha with rfl | rfl
    <;> grind [inv_one, inv_r, r.injEq, zmod_two_mul_eq_zero, neg_eq_of_add_eq_zero_right]

-- Helper: in ZMod (2*n), a + a = 0 implies a = 0 or a = n
private lemma zmod_add_self_eq_zero_cases {n : ℕ} (hn : 0 < n) (a : ZMod (2 * n))
    (ha : a + a = 0) : a = 0 ∨ a = (n : ZMod (2 * n)) := by
  have h2n : NeZero (2 * n) := ⟨by omega⟩

  -- a + a = 0 means 2 * a.val ≡ 0 (mod 2n)
  have hval : (a.val + a.val) % (2 * n) = 0 := by
    have := congr_arg ZMod.val ha
    grind [ZMod.val_add, ZMod.val_zero]

  -- So 2*n | a.val + a.val, hence n | a.val
  have hdvd : 2 * n ∣ a.val + a.val := by grind [Nat.dvd_of_mod_eq_zero]

  -- So n | a.val
  have hndvd : n ∣ a.val := by grind [Nat.mul_dvd_mul_iff_left]

  -- a.val < 2*n, so a.val = 0 or a.val = n
  have hlt := ZMod.val_lt a
  obtain ⟨k, hk⟩ := hndvd
  have hk_bound : k ≤ 1 := Nat.lt_succ_iff.mp (by nlinarith)
  interval_cases k
  · left
    rwa [Nat.mul_zero, ZMod.val_eq_zero] at hk
  · right
    rw [Nat.mul_one] at hk
    have : a = ((a.val : ℕ) : ZMod (2 * n)) := (ZMod.natCast_zmod_val a).symm
    rw [this, hk]

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

#check existsAndEq

example (a b c d e : ℕ) (h : a + b + c = a + d + e) : False := by
  simp at h
  grind

open DihedralGroup in
theorem my_thm_even (n : ℕ) (h4 : 2 ≤ n) :
    Subgroup.center (DihedralGroup (2*n)) = halfTurnClosure n := by
  have hn_pos : 0 < n := by omega
  have h2n_pos : 0 < 2 * n := by omega
  have h2n_ne : NeZero (2 * n) := ⟨by omega⟩
  ext x
  simp only [Subgroup.mem_center_iff, halfTurnClosure, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward: center → {1, r n}
    intro hx
    match x with
    | r i =>
      -- r i commutes with sr 0: r i * sr 0 = sr (0 - i) = sr (-i)
      -- and sr 0 * r i = sr (0 + i) = sr i
      -- So sr (-i) = sr i, hence -i = i, hence i + i = 0
      have h1 := sr.inj (hx (sr 0))
      simp only [zero_add, zero_sub] at h1
      -- h1 : -i = i, i.e. i = -i
      have hai : i + i = 0 := by linear_combination h1
      rcases zmod_add_self_eq_zero_cases hn_pos i hai with rfl | rfl <;> simp
    | sr i =>
      -- sr i * r 1 = sr (i + 1) and r 1 * sr i = sr (i - 1)
      -- So i + 1 = i - 1, hence 2 = 0 in ZMod (2n), contradiction
      have h1 := sr.inj (hx (r 1))
      simp only at h1
      -- h1 : i + 1 = i - 1
      have h2 : (2 : ZMod (2 * n)) = 0 := by linear_combination -h1
      exact absurd h2 (two_ne_zero_zmod n h4)
  · -- Backward: {1, r n} → center
    intro hx
    rcases hx with rfl | rfl
    · -- 1 is central
      intro y; rw [one_mul, mul_one]
    · -- r n is central
      intro y
      match y with
      | r j => simp [r_mul_r, add_comm]
      | sr j =>
        grind [zmod_two_mul_eq_zero, r_mul_sr, sr_mul_r]
