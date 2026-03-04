import Mathlib


namespace TendsTo

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

def Converges (a : ℕ → ℝ) : Prop := ∃ l, TendsTo a l

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
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ n) t) := by
  -- Assume the sequence converges to L
  intro L
  by_contra h_converges

  -- Then n is "near L" eventually
  -- i.e. there is a fixed B such that for all n ≥ B, n is "near L", i.e. |n - L| < 1/2
  rcases (h_converges (1/2) (by norm_num)) with ⟨B, hB⟩

  -- Take bad_n greater than L+1 and B.
  -- The first condition implies bad_n is "large"
  -- The second condition implies bad_n is "near L"
  have exists_bad_n : ∃ bad_n : ℕ, L + 1 < bad_n ∧ B ≤ bad_n := by
    use Nat.max (1 + Nat.ceil (L+1)) (1+B)
    refine And.intro ?left ?right

    case left =>
      rw [add_comm]
      simp only [Nat.add_max_add_left, Nat.cast_add, Nat.cast_one, Nat.cast_max, add_lt_add_iff_left,
        lt_sup_iff]
      left
      calc
        L < 1 + L := by linarith
        _ ≤ Nat.ceil (1 + L) := by exact Nat.le_ceil (1 + L)

    case right =>
      simp only [Nat.add_max_add_left]
      linarith [Nat.le_max_right (Nat.ceil (L + 1)) B]

  rcases exists_bad_n with ⟨bad_n, ⟨h1, h2⟩⟩

  -- bad_n is "near L"
  specialize hB bad_n h2
  dsimp at hB
  rw [abs_lt] at hB

  -- bad_n is "large"
  linarith

-- The sequence (1,0,1,0,...) does not converge to any real number
example : ∀ t : ℝ, ¬(TendsTo (fun n ↦ if n%2 = 0 then 1 else 0) t) := by
  -- Assume the sequence converges to L
  intro L
  by_contra h_converges

  -- Then |a_n - L| < 1/2 eventually (i.e. for all n ≥ B)
  rcases (h_converges (1/2) (by norm_num)) with ⟨B, hB⟩

  -- There exists a natural number n such that B ≤ n and n is even
  have : ∃ n, B ≤ n ∧ n % 2 = 0 := by
    have : B % 2 = 0 ∨ B % 2 = 1 := Nat.mod_two_eq_zero_or_one B
    rcases this with (l | r)
    use B
    use B+1
    constructor; repeat omega

  rcases this with ⟨n, ⟨l, n_even⟩⟩

  have n_plus_1_odd : (n + 1) % 2 = 1 := by omega

  have h1 := hB n l
  have h2 := hB (n+1) (by omega)

  dsimp at h1 h2

  rw [if_pos n_even] at h1
  rw [if_neg (Nat.mod_two_ne_zero.mpr n_plus_1_odd)] at h2

  simp only [abs_lt] at h1 h2
  linarith


end TendsTo