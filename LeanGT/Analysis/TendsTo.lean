import Mathlib.Tactic
import LeanTeXMathlib

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

def Converges (a : ℕ → ℝ) : Prop := ∃ l, TendsTo a l

-- Print `TendsTo f t` as `\lim f = t`
latex_pp_app_rules (const := TendsTo)
  | _, #[f, t] => do
    let f ← LeanTeX.latexPP f
    let t ← LeanTeX.latexPP t
    let f := f.protectLeft 66
    return "\\lim " ++ f ++ "=" ++ t |>.resetBP .Infinity .Infinity


latex_pp_app_rules (const := Nat.ceil)
  | _, #[_, _, _, e] => do
    let e ← LeanTeX.latexPP e
    return "\\lceil " ++ e ++ "\\rceil" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Nat.floor)
  | _, #[_, _, _, e] => do
    let e ← LeanTeX.latexPP e
    return "\\lfloor " ++ e ++ "\\rfloor" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Int.ceil)
  | _, #[_, _, _, e] => do
    let e ← LeanTeX.latexPP e
    return "\\lceil " ++ e ++ "\\rceil" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Int.floor)
  | _, #[_, _, _, e] => do
    let e ← LeanTeX.latexPP e
    return "\\lfloor " ++ e ++ "\\rfloor" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Max.max)
  | _, #[_, _, a, b] => do
    let a ← LeanTeX.latexPP a
    let b ← LeanTeX.latexPP b
    return "\\max(" ++ a ++ "," ++ b ++ ")" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Min.min)
  | _, #[_, _, a, b] => do
    let a ← LeanTeX.latexPP a
    let b ← LeanTeX.latexPP b
    return "\\min(" ++ a ++ "," ++ b ++ ")" |>.resetBP .Infinity .Infinity


theorem tendsTo_thirtyseven : TendsTo (fun _ ↦ 37) 37 := by
  intro ε hε
  use 100
  intro n hn
  norm_num
  exact hε

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun _ => c) c := by
  intro ε hε
  use 37
  intro n hn
  ring_nf
  norm_num
  exact hε

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) := by
  unfold TendsTo
  ring_nf
  exact h

/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  texify
  intro ε hε
  specialize ha ε hε
  cases' ha with B hB
  use B
  intro n hn
  specialize hB n hn
  rw [← abs_neg]
  ring_nf
  exact hB

example (ε : ℝ) (ε_pos : 0 < ε) (hn : 1 < ε*ε) : 1 < ε := by
  have := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr hn
  simp at this
  let t := (Real.sqrt_eq_iff_mul_self_eq_of_pos ε_pos).mpr rfl
  rw [t] at this
  exact this

-- Example 2.2.5: The sequence given by a_n = 1/sqrt(n) converges to 0
example : TendsTo (fun n ↦ 1/(Real.sqrt n)) 0 := by
  intro ε ε_pos

  -- Choose a natural number N satisfying N > 1/ε^2
  have exists_N : ∃ N : ℕ, (1/(ε*ε) < N) := by {
    use (1 + Nat.ceil (1/(ε*ε)))
    simp
    calc
      ε⁻¹ * ε⁻¹ ≤ ⌈ε⁻¹ * ε⁻¹⌉₊ := by exact Nat.le_ceil (ε⁻¹ * ε⁻¹)
      _ < 1 + ↑⌈ε⁻¹ * ε⁻¹⌉₊ := by simp
  }

  cases' exists_N with N N_cond

  have N_ge_0 : 0 < N := by
    rify
    have : 0 ≤ 1/(ε*ε) := by positivity
    linarith

  use N
  intro n hn

  rw [sub_zero, abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg n))]

  have hn : 1/(ε*ε) < n := by {
    rify at N_ge_0
    rify at hn
    linarith
  }

  have hn_canonical : 1 < n*ε*ε := by {
    have pos : 0 < ε*ε := by positivity
    have := (mul_lt_mul_right pos).mpr hn
    field_simp at this
    rw [mul_assoc]
    exact this
  }

  have hn_canonical_sqrt := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr hn_canonical
  simp at hn_canonical_sqrt

  simp
  -- rw?
  rw [inv_lt_iff_one_lt_mul₀']

  calc
    1 < Real.sqrt (n * ε * ε) := hn_canonical_sqrt
    _ = Real.sqrt (n * (ε * ε)) := by ring_nf
    _ = Real.sqrt n * Real.sqrt (ε*ε) := by simp
    _ = Real.sqrt n * ε := by {
      simp
      left
      exact (Real.sqrt_eq_iff_mul_self_eq_of_pos ε_pos).mpr rfl
    }

  simp
  linarith

-- Example 2.2.6: The sequence given by a_n = n+1/n converges to 1
example : TendsTo (fun n ↦ (n+1)/n) 1 := by
  intro ε ε_pos

  -- Choose a natural number N satisfying N > 1/ε^2
  have exists_N : ∃ N : ℕ, (1/ε < N) := by
    use (1 + Nat.ceil (1/ε))
    have : 1/ε ≤ ⌈1/ε⌉₊ := Nat.le_ceil (1/ε)
    push_cast
    linarith

  cases' exists_N with N N_cond

  use N
  intro n hn

  have n_pos : 0 < (n:ℝ) := by
    have : 0 < 1/ε := by positivity
    rify at hn
    linarith


  simp

  have : ((n + 1) / (n: ℝ)) - 1 = 1/n := by field_simp

  rw [this, abs_of_nonneg]

  have N_cond : 1 / ε < n := by
    rify at hn
    linarith

  have pos : 0 < (ε / n) := by positivity
  have N_cond := (mul_lt_mul_right pos).mpr N_cond
  field_simp at N_cond
  exact N_cond

  simp only [one_div, inv_nonneg, Nat.cast_nonneg]

-- The sequence (1,2,3...) not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ n) t) := by {
  intro L
  by_contra h_converges

  cases' (h_converges (1/2) (by norm_num)) with B hB

  have exists_bad_n : ∃ bad_n : ℕ, (L+1) < bad_n ∧ B < bad_n := by {
    use Nat.max (1 + Nat.ceil (L+1)) (1+B)
    constructor
    simp
    left
    calc
      L + 1 ≤ ↑⌈L + 1⌉₊ := by exact Nat.le_ceil (L + 1)
      _ < 1 + ↑⌈L + 1⌉₊ := by simp
    simp
  }

  cases' exists_bad_n with bad_n h_bad_n

  specialize hB bad_n

  cases' h_bad_n with h1 h2

  have hBn : B ≤ bad_n := by linarith

  apply hB at hBn

  have h1 : 1 < |↑bad_n - L| := by {
    rw [lt_abs]
    left
    linarith
  }

  linarith
}

-- The sequence (1,0,1,0,...) does not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ if n%2 = 0 then 1 else 0) t) := by
  intro L
  by_contra h_converges
  cases' (h_converges (1/2) (by norm_num)) with B hB

  have : ∃ n, B ≤ n ∧ n % 2 = 0 := by
    have : B % 2 = 0 ∨ B % 2 = 1 := Nat.mod_two_eq_zero_or_one B
    rcases this with (l | r)
    use B
    use B+1
    constructor; repeat omega

  cases' this with n hn
  cases' hn with l n_even
  have n_plus_1_odd : (n + 1) % 2 = 1 := by omega

  have h1 := hB n l
  have h2 := hB (n+1) (by omega)

  dsimp at h1 h2

  rw [if_pos n_even] at h1
  rw [if_neg (Nat.mod_two_ne_zero.mpr n_plus_1_odd)] at h2

  simp only [abs_lt] at h1 h2
  linarith
