import Playground.Pi.Basic
import Playground.Pi.Estimates
import Playground.Pi.Clausen
import Playground.Pi.Ramanujan
import Playground.Pi.Kummer
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# The Main Theorem (Milla, ch. 9)

The paper's ch. 9: the differential-equation form `thm42` and the
**Main Theorem** `hauptformel`,
```
1/(2π·Im τ) · √(J(τ)/(J(τ)−1))
  = ∑ n, ((1−s₂(τ))/6 + n) · (6n)!/((3n)!(n!)³) · (1728·J(τ))⁻ⁿ    (Im τ > 1.25)
```
where `√` is the principal branch (here: `Complex.cpow (1/2)`).

The intermediate propositions `thm35` (quasiperiod/period derivative relation) and
`thmglg10` (`η₁ − (3g₃/2g₂)s₂ = π/Im τ`) are stated in lattice language in the paper;
here the whole ch. 9 computation is carried out in modular language, replacing the
quasiperiod calculus by Ramanujan's derivative identities (`Ramanujan.lean`) applied
to Kummer's identity `E₄ = ₂F₁(1/12,5/12;1;1/J)⁴` (`Kummer.lean`): see the section
"The proof of `thm42`" below.

The branch of the square root is resolved *pointwise* in `thm42`:
`J/(J−1) = (G⁶/E₆)²` with `Re(G⁶/E₆) > 0` everywhere on `Region` (by explicit
estimates), and the principal square root of `w²` is `w` on the right half-plane
(`Complex.sq_cpow_two_inv`).  The connectedness workhorse `sq_eq_on_preconnected_eq`
originally planned for this step (PLAN A8) is kept for reference/reuse.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries Nat

open scoped Real

/-- `Gsq z = (₂F₁(1/12, 5/12; 1; z))²`, the square of Kummer's solution
(the function `G` in the proof of the Main Theorem). -/
def Gsq (z : ℂ) : ℂ := (₂F₁ (1 / 12 : ℂ) (5 / 12) 1 z) ^ 2

/-- The summand of the Main Theorem's series:
`((1−s₂(τ))/6 + n) · (6n)!/((3n)!(n!)³) · (1728·J(τ))⁻ⁿ`. -/
def mainSummand (τ : ℍ) (n : ℕ) : ℂ :=
  ((1 - s₂ τ) / 6 + n) * (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) /
    (1728 * J τ) ^ n

/-- The sharp factorial bound `(6n)!/((3n)!(n!)³) ≤ 1728ⁿ`, proved by induction from
the single-step estimate `(6n+1)(6n+3)(6n+5) ≤ (6n+6)³`. -/
private theorem factorial_ratio_le (n : ℕ) :
    (6 * n)! ≤ 1728 ^ n * ((3 * n)! * (n !) ^ 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e6 : (6 * (n + 1))! =
        ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
          * (6 * n)! := by
      have h : 6 * (n + 1) = 6 * n + 6 := by ring
      rw [h]; simp only [Nat.factorial_succ]; ring
    have e3 : (3 * (n + 1))! = ((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (3 * n)! := by
      have h : 3 * (n + 1) = 3 * n + 3 := by ring
      rw [h]; simp only [Nat.factorial_succ]; ring
    have e1 : ((n + 1)!) ^ 3 = (n + 1) ^ 3 * (n !) ^ 3 := by
      rw [Nat.factorial_succ]; ring
    have hPQ : (6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
        ≤ 1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3) := by
      have key : (6 * n + 1) * (6 * n + 3) * (6 * n + 5) ≤ (6 * n + 6) ^ 3 := by
        nlinarith [Nat.zero_le n]
      calc (6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
          = 24 * (n + 1) * (3 * n + 2) * (3 * n + 1)
              * ((6 * n + 1) * (6 * n + 3) * (6 * n + 5)) := by ring
        _ ≤ 24 * (n + 1) * (3 * n + 2) * (3 * n + 1) * (6 * n + 6) ^ 3 :=
              Nat.mul_le_mul le_rfl key
        _ = 1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3) := by ring
    calc (6 * (n + 1))!
        = ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
            * (6 * n)! := e6
      _ ≤ ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
            * (1728 ^ n * ((3 * n)! * (n !) ^ 3)) := Nat.mul_le_mul le_rfl ih
      _ = 1728 ^ n * (3 * n)! * (n !) ^ 3
            * ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2)
              * (6 * n + 1)) := by ring
      _ ≤ 1728 ^ n * (3 * n)! * (n !) ^ 3
            * (1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3)) :=
              Nat.mul_le_mul le_rfl hPQ
      _ = 1728 ^ (n + 1) * ((3 * (n + 1))! * ((n + 1)!) ^ 3) := by rw [e3, e1, pow_succ]; ring

/-- The Main Theorem's series converges absolutely on the region `Im τ > 1.25`
(ratio test: `(6n)!/((3n)!(n!)³) ≤ 1728ⁿ` and `‖1728·J‖ > 1728` on the region). -/
theorem summable_mainSummand {τ : ℍ} (hτ : τ ∈ Region) :
    Summable (mainSummand τ) := by
  set M : ℝ := ‖(1728 : ℂ) * J τ‖ with hMdef
  have hqpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hqb : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hM : (1728 : ℝ) < M := by
    have h1 : (1728 : ℝ) < 0.737 / ‖q τ‖ := by
      rw [lt_div_iff₀ hqpos]; nlinarith [hqb, hqpos]
    exact lt_trans h1 (theonaeherJ_lower hτ)
  have hMpos : 0 < M := lt_trans (by norm_num) hM
  set r : ℝ := 1728 / M with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hMpos]; exact hM
  set C : ℝ := ‖(1 - s₂ τ) / 6‖ with hCdef
  -- The majorant `(C + n)·rⁿ` is summable (geometric ⊕ `n·rⁿ`).
  have hgeom0 : Summable (fun n : ℕ => C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hgeom1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    simpa using h
  have hg : Summable (fun n : ℕ => (C + n) * r ^ n) := by
    have he : (fun n : ℕ => (C + (n : ℝ)) * r ^ n)
        = fun n : ℕ => C * r ^ n + (n : ℝ) * r ^ n := by ext n; ring
    rw [he]; exact hgeom0.add hgeom1
  refine Summable.of_norm_bounded hg ?_
  intro n
  have hden_pos : (0 : ℝ) < ((3 * n)! : ℝ) * ((n ! : ℝ)) ^ 3 := by positivity
  have hB : ‖((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)‖ ≤ (1728 : ℝ) ^ n := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
      Complex.norm_natCast, div_le_iff₀ hden_pos]
    calc ((6 * n)! : ℝ) ≤ ((1728 ^ n * ((3 * n)! * (n !) ^ 3) : ℕ) : ℝ) := by
            exact_mod_cast factorial_ratio_le n
      _ = 1728 ^ n * (((3 * n)! : ℝ) * ((n ! : ℝ)) ^ 3) := by push_cast; ring
  have hA : ‖(1 - s₂ τ) / 6 + (n : ℂ)‖ ≤ C + n := by
    calc ‖(1 - s₂ τ) / 6 + (n : ℂ)‖ ≤ ‖(1 - s₂ τ) / 6‖ + ‖(n : ℂ)‖ := norm_add_le _ _
      _ = C + n := by rw [Complex.norm_natCast, hCdef]
  unfold mainSummand
  rw [norm_div, norm_mul, norm_pow, ← hMdef]
  calc ‖(1 - s₂ τ) / 6 + (n : ℂ)‖
        * ‖((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)‖ / M ^ n
      ≤ (C + n) * 1728 ^ n / M ^ n := by gcongr
    _ = (C + n) * r ^ n := by rw [hrdef]; ring

/-- The branch-resolution workhorse (PLAN A8): two continuous functions on a
preconnected set whose squares agree, the second nonvanishing, agreeing at one
point, agree everywhere. -/
theorem sq_eq_on_preconnected_eq {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {f g : X → ℂ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hfg : ∀ x ∈ s, f x ^ 2 = g x ^ 2) (hg0 : ∀ x ∈ s, g x ≠ 0)
    {x₀ : X} (hx₀ : x₀ ∈ s) (h₀ : f x₀ = g x₀) :
    ∀ x ∈ s, f x = g x := by
  have hpc : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hfc : Continuous fun x : s => f x :=
    hf.comp_continuous continuous_subtype_val fun x => x.2
  have hgc : Continuous fun x : s => g x :=
    hg.comp_continuous continuous_subtype_val fun x => x.2
  -- The "equal" set `A` and the "opposite" set `B` inside the subtype `s`.
  set A : Set s := {x | f x = g x} with hA
  set B : Set s := {x | f x = -g x} with hB
  have hBclosed : IsClosed B := by
    have h : IsClosed {x : s | (fun x : s => f x + g x) x = 0} :=
      isClosed_eq (hfc.add hgc) continuous_const
    convert h using 2 with x
    simp [eq_neg_iff_add_eq_zero]
  -- `A ∪ B = univ` since `(f - g)(f + g) = f² - g² = 0`.
  have hcover : A ∪ B = Set.univ := by
    ext x
    simp only [Set.mem_union, hA, hB, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hprod : (f x - g x) * (f x + g x) = 0 := by
      have h := hfg x x.2; linear_combination h
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  -- `A` and `B` are disjoint: `f x = g x` and `f x = -g x` force `g x = 0`.
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_iff]
    rintro x ⟨hxA, hxB⟩
    simp only [hA, hB, Set.mem_setOf_eq] at hxA hxB
    exact absurd (by linear_combination (hxB - hxA) / (2 : ℂ)) (hg0 x x.2)
  -- Hence `Aᶜ = B`, so `A` is clopen; being nonempty (`x₀`) it is everything.
  have hAc : Aᶜ = B := by
    ext x
    constructor
    · intro hx
      exact ((hcover ▸ Set.mem_univ x : x ∈ A ∪ B)).resolve_left hx
    · intro hxB hxA
      exact Set.disjoint_iff.mp hdisj ⟨hxA, hxB⟩
  have hAclopen : IsClopen A :=
    ⟨isClosed_eq hfc hgc, isClosed_compl_iff.mp (hAc ▸ hBclosed)⟩
  have hAuniv : A = Set.univ :=
    hAclopen.eq_univ ⟨⟨x₀, hx₀⟩, h₀⟩
  intro x hx
  have : (⟨x, hx⟩ : s) ∈ A := hAuniv ▸ Set.mem_univ _
  simpa [hA] using this

/-- The region `Im τ > 1.25` is preconnected. -/
theorem isPreconnected_Region : IsPreconnected (Region : Set ℍ) := by
  rw [← (UpperHalfPlane.isEmbedding_coe.toIsInducing).isPreconnected_image]
  have himg : ((↑) : ℍ → ℂ) '' Region = {z : ℂ | (5 : ℝ) / 4 < z.im} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      rw [UpperHalfPlane.coe_im]; exact hτ
    · intro hz
      exact ⟨⟨z, lt_trans (by norm_num) hz⟩, hz, rfl⟩
  rw [himg]
  exact (convex_halfSpace_im_gt (5 / 4)).isPreconnected

/-! ### The reduction `hauptformel` ← `thm42`

Milla's derivation of the Main Theorem from `thm42` is the term-by-term differentiation
of the series `darst` (`hyp2F1_sq_eq_tsum`): with `cₙ = (6n)!/((3n)!(n!)³·1728ⁿ)` and
`w = 1/J` (so `‖w‖ < 1` on the region),
`(1−s₂)/6·G(w) + w·G′(w) = ∑ ((1−s₂)/6 + n)·cₙ·wⁿ = ∑ mainSummand`. -/

/-- The coefficient `(6n)!/((3n)!(n!)³·1728ⁿ)` of the power series of `Gsq`. -/
private def mainCoeff (n : ℕ) : ℂ :=
  ((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n !: ℕ) : ℂ) ^ 3 * 1728 ^ n)

private lemma norm_mainCoeff_le_one (n : ℕ) : ‖mainCoeff n‖ ≤ 1 := by
  have hden_pos : (0 : ℝ) < ((3 * n)! : ℝ) * ((n ! : ℝ)) ^ 3 * 1728 ^ n := by positivity
  rw [mainCoeff, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
    Complex.norm_natCast, Complex.norm_natCast, Complex.norm_ofNat, div_le_one hden_pos]
  calc ((6 * n)! : ℝ) ≤ ((1728 ^ n * ((3 * n)! * (n !) ^ 3) : ℕ) : ℝ) := by
        exact_mod_cast factorial_ratio_le n
    _ = ((3 * n)! : ℝ) * ((n ! : ℝ)) ^ 3 * 1728 ^ n := by push_cast; ring

/-- Paper Thm. `darst` in `Gsq`/`mainCoeff` form: `Gsq z = ∑ cₙ zⁿ` for `‖z‖ < 1`. -/
private lemma Gsq_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    Gsq z = ∑' n : ℕ, mainCoeff n * z ^ n := by
  have h := hyp2F1_sq_eq_tsum hz
  rw [show Gsq z = hyp2F1 z ^ 2 from rfl, h]
  refine tsum_congr fun n => ?_
  have h3n : ((3 * n)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hn : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h12 : ((12 : ℂ)) ^ (3 * n) = 1728 ^ n := by rw [pow_mul]; norm_num
  rw [mainCoeff, h12]
  field_simp

/-- Term-by-term differentiation of `∑ cₙ wⁿ` on the open unit disc (specialized
re-derivation of the private `DiscSummable` toolkit of `Clausen.lean`, simplified by
the bound `‖cₙ‖ ≤ 1`). -/
private lemma hasDerivAt_tsum_mainCoeff {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, mainCoeff n * w ^ n)
      (∑' n : ℕ, mainCoeff n * ((n : ℂ) * z ^ (n - 1))) z := by
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  have hu : Summable fun n : ℕ => (n : ℝ) * ρ ^ (n - 1) := by
    have h : Summable fun n : ℕ => (n : ℝ) * ρ ^ n := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ρ)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hρpos.le]; exact hρ1)
      simpa using this
    refine (h.mul_left ρ⁻¹).congr fun n => ?_
    rcases n with _ | k
    · simp
    · rw [Nat.succ_sub_one, pow_succ]
      push_cast
      field_simp
  have hgderiv : ∀ (n : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) ρ →
      HasDerivAt (fun w : ℂ => mainCoeff n * w ^ n) (mainCoeff n * ((n : ℂ) * y ^ (n - 1))) y :=
    fun n y _ => (hasDerivAt_pow n y).const_mul (mainCoeff n)
  have hgbound : ∀ (n : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) ρ →
      ‖mainCoeff n * ((n : ℂ) * y ^ (n - 1))‖ ≤ (n : ℝ) * ρ ^ (n - 1) := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    calc ‖mainCoeff n * ((n : ℂ) * y ^ (n - 1))‖
        = ‖mainCoeff n‖ * ((n : ℝ) * ‖y‖ ^ (n - 1)) := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ 1 * ((n : ℝ) * ρ ^ (n - 1)) := by
          gcongr
          exact norm_mainCoeff_le_one n
      _ = (n : ℝ) * ρ ^ (n - 1) := one_mul _
  have hg0 : Summable fun n : ℕ => mainCoeff n * (0 : ℂ) ^ n := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    rw [Finset.mem_singleton] at hn
    rw [zero_pow hn, mul_zero]
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hgderiv hgbound
    (Metric.mem_ball_self hρpos) hg0
    (by simpa only [Metric.mem_ball, dist_zero_right] using hzρ)

/-- `Gsq′(z) = ∑ n·cₙ·zⁿ⁻¹` for `‖z‖ < 1`. -/
private lemma deriv_Gsq_eq {z : ℂ} (hz : ‖z‖ < 1) :
    deriv Gsq z = ∑' n : ℕ, mainCoeff n * ((n : ℂ) * z ^ (n - 1)) := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hev : Gsq =ᶠ[nhds z] fun w => ∑' n : ℕ, mainCoeff n * w ^ n := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact Gsq_eq_tsum hw
  rw [hev.deriv_eq]
  exact (hasDerivAt_tsum_mainCoeff hz).deriv

/-- `mainSummand` in `mainCoeff · wⁿ` form, `w = 1/J`. -/
private lemma mainSummand_eq {τ : ℍ} (hJ0 : J τ ≠ 0) (n : ℕ) :
    mainSummand τ n = ((1 - s₂ τ) / 6 + n) * (mainCoeff n * (1 / J τ) ^ n) := by
  have h3n : ((3 * n)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hn : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  have hJn : J τ ^ n ≠ 0 := pow_ne_zero n hJ0
  rw [mainSummand, mainCoeff, mul_pow, one_div, inv_pow]
  field_simp

/-! ### The proof of `thm42`

Following the modular-forms reformulation of the paper's ch. 9 computation: with
`G = ₂F₁(1/12,5/12;1;1/J)` (so `E₄ = G⁴` by Kummer's Thm. `omegastrich`), Ramanujan's
identity `D E₄ = (E₂E₄−E₆)/3` and the derivative `D J = −J·E₆/E₄` (from `D E₄`, `D E₆`)
combine via the chain rule to `E₂ = E₆/E₄ + 12G³G′E₆/(E₄²J)`.  Substituting this and
`E₄ = G⁴` into the right-hand side of `thm42` collapses it to `G⁶/(2πE₆·Im τ)`; and the
left-hand side equals the same value because `J/(J−1) = E₄³/E₆² = (G⁶/E₆)²` and the
principal square root of `w²` is `w` whenever `Re w > 0` — which holds here by the
explicit estimates `‖G²−1‖ ≤ 0.15` (from the `Gsq` power series, `‖1/J‖ < 1/1.096`)
and `‖E₆−1‖ ≤ 0.199` (from `Estimates.lean`).  This replaces the paper's
continuity/connectedness branch argument by a pointwise right-half-plane one. -/

/-- One step of the ratio bound behind `factorial_ratio_le`, in product form: the
coefficients `(6n)!/((3n)!(n!)³1728ⁿ)` are (weakly) decreasing. -/
private theorem factorial_ratio_succ (n : ℕ) :
    (6 * (n + 1))! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)
      ≤ (6 * n)! * ((3 * (n + 1))! * ((n + 1)!) ^ 3 * 1728 ^ (n + 1)) := by
  have e6 : (6 * (n + 1))! =
      ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
        * (6 * n)! := by
    have h : 6 * (n + 1) = 6 * n + 6 := by ring
    rw [h]; simp only [Nat.factorial_succ]; ring
  have e3 : (3 * (n + 1))! = ((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (3 * n)! := by
    have h : 3 * (n + 1) = 3 * n + 3 := by ring
    rw [h]; simp only [Nat.factorial_succ]; ring
  have e1 : ((n + 1)!) ^ 3 = (n + 1) ^ 3 * (n !) ^ 3 := by
    rw [Nat.factorial_succ]; ring
  have hPQ : (6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
      ≤ 1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3) := by
    have key : (6 * n + 1) * (6 * n + 3) * (6 * n + 5) ≤ (6 * n + 6) ^ 3 := by
      nlinarith [Nat.zero_le n]
    calc (6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
        = 24 * (n + 1) * (3 * n + 2) * (3 * n + 1)
            * ((6 * n + 1) * (6 * n + 3) * (6 * n + 5)) := by ring
      _ ≤ 24 * (n + 1) * (3 * n + 2) * (3 * n + 1) * (6 * n + 6) ^ 3 :=
            Nat.mul_le_mul le_rfl key
      _ = 1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3) := by ring
  calc (6 * (n + 1))! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)
      = ((6 * n + 6) * (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1))
          * ((6 * n)! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)) := by rw [e6]; ring
    _ ≤ (1728 * (((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) * (n + 1) ^ 3))
          * ((6 * n)! * ((3 * n)! * (n !) ^ 3 * 1728 ^ n)) := Nat.mul_le_mul hPQ le_rfl
    _ = (6 * n)! * ((3 * (n + 1))! * ((n + 1)!) ^ 3 * 1728 ^ (n + 1)) := by
        rw [e3, e1, pow_succ]; ring

private lemma norm_mainCoeff_eq (n : ℕ) :
    ‖mainCoeff n‖ = ((6 * n)! : ℝ) / (((3 * n)! : ℝ) * ((n ! : ℕ) : ℝ) ^ 3 * 1728 ^ n) := by
  rw [mainCoeff, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
    Complex.norm_natCast, Complex.norm_natCast, Complex.norm_ofNat]

private lemma norm_mainCoeff_succ_le (n : ℕ) : ‖mainCoeff (n + 1)‖ ≤ ‖mainCoeff n‖ := by
  rw [norm_mainCoeff_eq, norm_mainCoeff_eq,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast factorial_ratio_succ n

private lemma norm_mainCoeff_antitone : Antitone fun n => ‖mainCoeff n‖ :=
  antitone_nat_of_succ_le norm_mainCoeff_succ_le

/-- The quantitative bound behind the branch argument: on `‖z‖ ≤ 0.9125` (which covers
`z = 1/J` on `Region`, where `‖J‖ > 1.096`), `Gsq z = ₂F₁(1/12,5/12;1;z)²` stays within
`0.15` of `1`.  Six explicit terms of the (positive, decreasing) coefficient sequence
`mainCoeff` plus a geometric tail. -/
private lemma norm_Gsq_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 0.9125) : ‖Gsq z - 1‖ ≤ 0.15 := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- summability of the series and of its norms
  have hSnorm : Summable fun n : ℕ => ‖mainCoeff n * z ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one hz0 hz1)
    rw [norm_mul, norm_pow]
    calc ‖mainCoeff n‖ * ‖z‖ ^ n ≤ 1 * ‖z‖ ^ n := by
          gcongr; exact norm_mainCoeff_le_one n
      _ = ‖z‖ ^ n := one_mul _
  have hS : Summable fun n : ℕ => mainCoeff n * z ^ n := hSnorm.of_norm
  -- peel off the constant term `mainCoeff 0 = 1`
  have h0 : mainCoeff 0 * z ^ 0 = 1 := by
    rw [mainCoeff]
    norm_num [Nat.factorial]
  have hsplit : Gsq z - 1 = ∑' n : ℕ, mainCoeff (n + 1) * z ^ (n + 1) := by
    rw [Gsq_eq_tsum hz1, hS.tsum_eq_zero_add, h0]
    ring
  rw [hsplit]
  have hSnorm1 : Summable fun n : ℕ => ‖mainCoeff (n + 1) * z ^ (n + 1)‖ :=
    (summable_nat_add_iff 1).mpr hSnorm
  refine le_trans (norm_tsum_le_tsum_norm hSnorm1) ?_
  -- split off the first six terms
  rw [← hSnorm1.sum_add_tsum_nat_add 6]
  -- termwise numeric bound
  have hterm : ∀ n : ℕ, ∀ c : ℝ, ‖mainCoeff n‖ ≤ c →
      ‖mainCoeff n * z ^ n‖ ≤ c * 0.9125 ^ n := by
    intro n c hc
    rw [norm_mul, norm_pow]
    exact mul_le_mul hc (pow_le_pow_left₀ hz0 hz n) (by positivity)
      (le_trans (norm_nonneg _) hc)
  have hd1 : ‖mainCoeff 1‖ ≤ 0.0695 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  have hd2 : ‖mainCoeff 2‖ ≤ 0.0279 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  have hd3 : ‖mainCoeff 3‖ ≤ 0.01584 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  have hd4 : ‖mainCoeff 4‖ ≤ 0.01051 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  have hd5 : ‖mainCoeff 5‖ ≤ 0.00762 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  have hd6 : ‖mainCoeff 6‖ ≤ 0.00585 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  have hd7 : ‖mainCoeff 7‖ ≤ 0.00467 := by rw [norm_mainCoeff_eq]; norm_num [Nat.factorial]
  -- head: six explicit terms
  have hhead : ∑ i ∈ Finset.range 6, ‖mainCoeff (i + 1) * z ^ (i + 1)‖ ≤
      0.0695 * 0.9125 ^ 1 + 0.0279 * 0.9125 ^ 2 + 0.01584 * 0.9125 ^ 3 +
        0.01051 * 0.9125 ^ 4 + 0.00762 * 0.9125 ^ 5 + 0.00585 * 0.9125 ^ 6 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (hterm 1 _ hd1) (hterm 2 _ hd2)) (hterm 3 _ hd3)) (hterm 4 _ hd4))
      (hterm 5 _ hd5)) (hterm 6 _ hd6)
  -- geometric tail, using that `‖mainCoeff n‖` is decreasing
  have htail : ∑' i : ℕ, ‖mainCoeff (i + 6 + 1) * z ^ (i + 6 + 1)‖ ≤
      0.00467 * 0.9125 ^ 7 * (1 - 0.9125)⁻¹ := by
    have hmaj : ∀ i : ℕ, ‖mainCoeff (i + 6 + 1) * z ^ (i + 6 + 1)‖ ≤
        (0.00467 * 0.9125 ^ 7) * 0.9125 ^ i := by
      intro i
      have hc : ‖mainCoeff (i + 6 + 1)‖ ≤ 0.00467 :=
        le_trans (norm_mainCoeff_antitone (by omega : 7 ≤ i + 6 + 1)) hd7
      calc ‖mainCoeff (i + 6 + 1) * z ^ (i + 6 + 1)‖ ≤ 0.00467 * 0.9125 ^ (i + 6 + 1) :=
            hterm _ _ hc
        _ = (0.00467 * 0.9125 ^ 7) * 0.9125 ^ i := by ring
    have hgeom : Summable fun i : ℕ => (0.00467 * 0.9125 ^ 7 : ℝ) * 0.9125 ^ i :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    calc ∑' i : ℕ, ‖mainCoeff (i + 6 + 1) * z ^ (i + 6 + 1)‖
        ≤ ∑' i : ℕ, (0.00467 * 0.9125 ^ 7 : ℝ) * 0.9125 ^ i :=
          ((summable_nat_add_iff 6).mpr hSnorm1).tsum_le_tsum hmaj hgeom
      _ = (0.00467 * 0.9125 ^ 7) * (1 - 0.9125)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  refine le_trans (add_le_add hhead htail) ?_
  norm_num

/-- On `Region`, `E₆` is within `0.199` of `1` (from the truncation bounds of
`Estimates.lean`). -/
private lemma norm_E₆_sub_one_le {τ : ℍ} (hτ : τ ∈ Region) : ‖E₆ τ - 1‖ ≤ 0.199 := by
  set Q := ‖q τ‖ with hQdef
  have hQpos : 0 < Q := norm_q_pos τ
  have hQ : Q < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have htail : ‖eisensteinTail 5 3 τ‖ ≤ 245.6 * Q ^ 3 := norm_eisensteinTail_sigma₅ hτ
  have hqq : ‖q τ + (33 : ℂ) * q τ ^ 2‖ ≤ Q + 33 * Q ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  have heq : E₆ τ - 1 = -(504 * (q τ + 33 * q τ ^ 2)) - 504 * eisensteinTail 5 3 τ := by
    rw [E₆_eq_trunc τ, E₆trunc]; ring
  rw [heq]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_ofNat]
  nlinarith [norm_nonneg (eisensteinTail 5 3 τ), pow_pos hQpos 2, pow_pos hQpos 3]

/-- If `a` is closer to `b` than `b` is to `0`, then `a/b` lies in the right half-plane. -/
private lemma re_div_pos_of_norm_sub_lt {a b : ℂ} (hb : ‖a - b‖ < ‖b‖) : 0 < (a / b).re := by
  have hbn : 0 < ‖b‖ := lt_of_le_of_lt (norm_nonneg _) hb
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbn
  have h1 : a / b - 1 = (a - b) / b := by field_simp
  have h2 : ‖a / b - 1‖ < 1 := by
    rw [h1, norm_div, div_lt_one hbn]; exact hb
  have h3 : |(a / b - 1).re| ≤ ‖a / b - 1‖ := Complex.abs_re_le_norm _
  have h4 : (a / b - 1).re = (a / b).re - 1 := by simp
  have h5 := (abs_le.mp h3).1
  linarith

/-- `hyp2F1` is analytic on the open unit disc (same argument as in `Kummer.lean`). -/
private theorem hyp2F1_analyticAt {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ hyp2F1 w := by
  have habc : ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 12 : ℂ) ∧ (kn : ℂ) ≠ -(5 / 12 : ℂ) ∧ (kn : ℂ) ≠ -1 := by
    intro kn
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h0 : ((12 * kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((12 * kn + 5 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
      rw [Nat.cast_eq_zero] at h0; omega
  have hrad : (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1).radius = 1 :=
    ordinaryHypergeometricSeries_radius_eq_one ℂ (a := 1 / 12) (b := 5 / 12) (c := 1) habc
  have hfps := (ordinaryHypergeometricSeries ℂ (1 / 12 : ℂ) (5 / 12) 1).hasFPowerSeriesOnBall
    (by rw [hrad]; exact one_pos)
  rw [hrad] at hfps
  have hmem : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [mem_eball_zero_iff, show ‖w‖ₑ = (‖w‖₊ : ENNReal) from rfl]; exact_mod_cast hw
  exact hfps.analyticAt_of_mem hmem

/-- `E₄ ∘ ofComplex` has the derivative given by Ramanujan's identity, as `HasDerivAt`. -/
private lemma hasDerivAt_E₄_comp (τ : ℍ) :
    HasDerivAt ((⇑E₄) ∘ ofComplex) (2 * π * Complex.I / 3 * (E2 τ * E₄ τ - E₆ τ)) ↑τ := by
  have hd : DifferentiableAt ℂ ((⇑E₄) ∘ ofComplex) ↑τ :=
    mdifferentiableAt_iff.mp ((ModularFormClass.holo E₄) τ)
  exact deriv_comp_ofComplex_E₄ τ ▸ hd.hasDerivAt

/-- `E₆ ∘ ofComplex` has the derivative given by Ramanujan's identity, as `HasDerivAt`. -/
private lemma hasDerivAt_E₆_comp (τ : ℍ) :
    HasDerivAt ((⇑E₆) ∘ ofComplex) (π * Complex.I * (E2 τ * E₆ τ - E₄ τ ^ 2)) ↑τ := by
  have hd : DifferentiableAt ℂ ((⇑E₆) ∘ ofComplex) ↑τ :=
    mdifferentiableAt_iff.mp ((ModularFormClass.holo E₆) τ)
  exact deriv_comp_ofComplex_E₆ τ ▸ hd.hasDerivAt

/-- The `τ`-derivative of Klein's `J`: `(J ∘ ofComplex)′ = −2πi·E₄²E₆/(E₄³−E₆²)`
(equivalently `D J = −J·E₆/E₄`), by the quotient rule from Ramanujan's identities —
the `E₂` terms cancel. -/
private lemma hasDerivAt_J_comp (τ : ℍ) :
    HasDerivAt (J ∘ ofComplex)
      (-(2 * π * Complex.I) * E₄ τ ^ 2 * E₆ τ / (E₄ τ ^ 3 - E₆ τ ^ 2)) ↑τ := by
  have h4 := hasDerivAt_E₄_comp τ
  have h6 := hasDerivAt_E₆_comp τ
  have hcomp4 : ((⇑E₄) ∘ ofComplex) ↑τ = E₄ τ := by simp [Function.comp_apply, ofComplex_apply]
  have hcomp6 : ((⇑E₆) ∘ ofComplex) ↑τ = E₆ τ := by simp [Function.comp_apply, ofComplex_apply]
  have hden : ((⇑E₄ ∘ ofComplex) ↑τ) ^ 3 - ((⇑E₆ ∘ ofComplex) ↑τ) ^ 2 ≠ 0 := by
    rw [hcomp4, hcomp6]; exact E₄_cube_sub_E₆_sq_ne_zero τ
  have hquot := (h4.pow 3).div ((h4.pow 3).sub (h6.pow 2)) hden
  have heq : (J ∘ ofComplex) = fun z =>
      ((⇑E₄ ∘ ofComplex) z) ^ 3 / (((⇑E₄ ∘ ofComplex) z) ^ 3 - ((⇑E₆ ∘ ofComplex) z) ^ 2) := rfl
  rw [heq]
  refine hquot.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.sub_apply, Function.comp_apply, ofComplex_apply]
  have hd0 : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  field_simp
  ring

/-- Milla's ch. 9 computation `omegastrich′`, in modular language: differentiating
Kummer's identity `E₄ = G⁴` (`G = ₂F₁(1/12,5/12;1;1/J)`) with the chain rule and
comparing with Ramanujan's `D E₄` gives `E₂·E₄²J = E₆E₄J + 12G³G′E₆` on `Region`. -/
private lemma E2_mul_eq_of_mem_Region {τ : ℍ} (hτ : τ ∈ Region) :
    E2 τ * (E₄ τ ^ 2 * J τ) =
      E₆ τ * (E₄ τ * J τ) +
        12 * hyp2F1 (J τ)⁻¹ ^ 3 * deriv hyp2F1 (J τ)⁻¹ * E₆ τ := by
  -- non-vanishing facts
  have hJnorm : 1 < ‖J τ‖ := one_lt_norm_J hτ
  have hJ0 : J τ ≠ 0 := by
    intro h; rw [h, norm_zero] at hJnorm; norm_num at hJnorm
  have hden : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have hE₄0 : E₄ τ ≠ 0 := by
    intro h
    apply hJ0
    rw [J, h]
    simp
  have hJmul : J τ * (E₄ τ ^ 3 - E₆ τ ^ 2) = E₄ τ ^ 3 := by
    rw [J]; field_simp
  have hu : ‖(J τ)⁻¹‖ < 1 := norm_inv_J_lt_one hτ
  have h2πI : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- derivative of z ↦ ((J ∘ ofComplex) z)⁻¹ at ↑τ, with the simplified value
  have hJc := hasDerivAt_J_comp τ
  have hJcτ : (J ∘ ofComplex) ↑τ = J τ := by simp [Function.comp_apply, ofComplex_apply]
  have hJinv : HasDerivAt (fun z => ((J ∘ ofComplex) z)⁻¹)
      (2 * (π : ℂ) * Complex.I * E₆ τ / (E₄ τ * J τ)) ↑τ := by
    have h := hJc.inv (by rw [hJcτ]; exact hJ0)
    rw [hJcτ] at h
    refine h.congr_deriv ?_
    field_simp
    linear_combination (-(E₆ τ)) * hJmul
  -- derivative of hyp2F1 at (J τ)⁻¹
  have hG : HasDerivAt hyp2F1 (deriv hyp2F1 (J τ)⁻¹) (((J ∘ ofComplex) ↑τ)⁻¹) := by
    rw [hJcτ]
    exact (hyp2F1_analyticAt hu).differentiableAt.hasDerivAt
  -- the composite z ↦ hyp2F1(((J ∘ ofComplex) z)⁻¹)⁴ and its derivative
  have hcomp := (hG.comp (↑τ : ℂ) hJinv).pow 4
  -- `E₄ ∘ ofComplex` agrees with the composite near ↑τ (Kummer's theorem on `Region`)
  have hopen : IsOpen {z : ℂ | 5 / 4 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hmem : (↑τ : ℂ) ∈ {z : ℂ | 5 / 4 < z.im} := by
    simpa only [Region, Set.mem_setOf_eq, UpperHalfPlane.coe_im] using hτ
  have hev : (⇑E₄ ∘ ofComplex) =ᶠ[nhds (↑τ : ℂ)]
      fun z => hyp2F1 (((J ∘ ofComplex) z)⁻¹) ^ 4 := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz0 : 0 < z.im := lt_trans (by norm_num) hz
    have hzR : ofComplex z ∈ Region := by
      rw [ofComplex_apply_of_im_pos hz0]
      exact hz
    simpa only [Function.comp_apply] using E₄_eq_hyp2F1_pow_four hzR
  -- equate the two computations of `deriv (E₄ ∘ ofComplex)` at ↑τ
  have hkey : 2 * (π : ℂ) * Complex.I / 3 * (E2 τ * E₄ τ - E₆ τ) =
      4 * hyp2F1 (J τ)⁻¹ ^ 3 *
        (deriv hyp2F1 (J τ)⁻¹ * (2 * (π : ℂ) * Complex.I * E₆ τ / (E₄ τ * J τ))) := by
    have h1 : deriv (⇑E₄ ∘ ofComplex) ↑τ =
        deriv (fun z => hyp2F1 (((J ∘ ofComplex) z)⁻¹) ^ 4) ↑τ := hev.deriv_eq
    have h2 : deriv (fun z => hyp2F1 (((J ∘ ofComplex) z)⁻¹) ^ 4) ↑τ =
        (4 : ℕ) * (hyp2F1 ∘ fun z => ((J ∘ ofComplex) z)⁻¹) ↑τ ^ (4 - 1) *
          (deriv hyp2F1 (J τ)⁻¹ * (2 * (π : ℂ) * Complex.I * E₆ τ / (E₄ τ * J τ))) :=
      hcomp.deriv
    rw [← deriv_comp_ofComplex_E₄ τ, h1, h2]
    simp only [Function.comp_apply, ofComplex_apply]
    push_cast
    ring
  -- solve for E₂
  field_simp at hkey
  rw [one_div] at hkey
  refine mul_left_cancel₀ h2πI ?_
  linear_combination (2 * (π : ℂ) * Complex.I) * hkey

/-- Milla's Prop. `thm42`: the differential equation
`1/(2π·Im τ)·√(J/(J−1)) = (1−s₂)/6 · G(1/J) + (1/J)·G′(1/J)`
for `Im τ > 1.25`, with the principal branch of the square root.  The branch is
resolved pointwise: `J/(J−1) = (G⁶/E₆)²` with `Re(G⁶/E₆) > 0` on all of `Region`
(by the explicit estimates), and the principal square root of `w²` is `w` on the
right half-plane. -/
theorem thm42 {τ : ℍ} (hτ : τ ∈ Region) :
    1 / (2 * (π : ℂ) * (τ.im : ℂ)) * (J τ / (J τ - 1)) ^ (1 / 2 : ℂ) =
      (1 - s₂ τ) / 6 * Gsq (1 / J τ) + 1 / J τ * deriv Gsq (1 / J τ) := by
  show 1 / (2 * (π : ℂ) * (τ.im : ℂ)) * (J τ / (J τ - 1)) ^ (1 / 2 : ℂ) =
      (1 - s₂ τ) / 6 * (hyp2F1 (1 / J τ) ^ 2) +
        1 / J τ * deriv (fun w => hyp2F1 w ^ 2) (1 / J τ)
  -- basic non-vanishing facts
  have hJnorm : (1.096 : ℝ) < ‖J τ‖ := theonaeherJ_norm_J hτ
  have hJ0 : J τ ≠ 0 := by
    intro h; rw [h, norm_zero] at hJnorm; norm_num at hJnorm
  have hden : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  have hE₄0 : E₄ τ ≠ 0 := by
    intro h
    apply hJ0
    rw [J, h]
    simp
  have hE₆0 : E₆ τ ≠ 0 := E₆_ne_zero_of_mem_Region hτ
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have him0 : ((τ.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt τ.im_pos)
  have hJmul : J τ * (E₄ τ ^ 3 - E₆ τ ^ 2) = E₄ τ ^ 3 := by
    rw [J]; field_simp
  have hu : ‖(J τ)⁻¹‖ < 1 := norm_inv_J_lt_one hτ
  -- Kummer's theorem and the E₂ identity
  have hE₄ : E₄ τ = hyp2F1 (J τ)⁻¹ ^ 4 := E₄_eq_hyp2F1_pow_four hτ
  have hG0 : hyp2F1 (J τ)⁻¹ ≠ 0 := by
    intro h
    apply hE₄0
    rw [hE₄, h]
    ring
  have hE2 := E2_mul_eq_of_mem_Region hτ
  -- the derivative of w ↦ hyp2F1(w)² at 1/J
  have hone : (1 : ℂ) / J τ = (J τ)⁻¹ := one_div _
  have hderivsq : deriv (fun w => hyp2F1 w ^ 2) (1 / J τ) =
      2 * hyp2F1 (J τ)⁻¹ * deriv hyp2F1 (J τ)⁻¹ := by
    rw [hone]
    have hG : HasDerivAt hyp2F1 (deriv hyp2F1 (J τ)⁻¹) (J τ)⁻¹ :=
      (hyp2F1_analyticAt hu).differentiableAt.hasDerivAt
    have h2 : deriv (fun w => hyp2F1 w ^ 2) (J τ)⁻¹ =
        (2 : ℕ) * hyp2F1 (J τ)⁻¹ ^ (2 - 1) * deriv hyp2F1 (J τ)⁻¹ := (hG.pow 2).deriv
    rw [h2]
    norm_num
  -- `J/(J−1)` is the square of `G⁶/E₆`
  have hsq : J τ / (J τ - 1) = (hyp2F1 (J τ)⁻¹ ^ 6 / E₆ τ) ^ 2 := by
    have hJ1 : J τ - 1 ≠ 0 := by
      intro h
      have h2 : (J τ - 1) * (E₄ τ ^ 3 - E₆ τ ^ 2) = E₆ τ ^ 2 := by linear_combination hJmul
      rw [h, zero_mul] at h2
      exact hE₆0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.symm)
    have hJmul' := hJmul
    rw [hE₄] at hJmul'
    rw [div_pow, div_eq_div_iff hJ1 (pow_ne_zero 2 hE₆0)]
    linear_combination -hJmul'
  -- positivity of `Re(G⁶/E₆)`: quantitative bounds
  have hznorm : ‖(J τ)⁻¹‖ ≤ 0.9125 := by
    rw [norm_inv]
    have h2 : (1.096 : ℝ)⁻¹ ≤ 0.9125 := by norm_num
    exact le_trans (inv_anti₀ (by norm_num) hJnorm.le) h2
  have hb2 : ‖hyp2F1 (J τ)⁻¹ ^ 2 - 1‖ ≤ 0.15 := norm_Gsq_sub_one_le hznorm
  have hb6 : ‖hyp2F1 (J τ)⁻¹ ^ 6 - 1‖ ≤ 0.520875 := by
    have hexp : hyp2F1 (J τ)⁻¹ ^ 6 - 1 =
        (hyp2F1 (J τ)⁻¹ ^ 2 - 1) ^ 3 + 3 * (hyp2F1 (J τ)⁻¹ ^ 2 - 1) ^ 2 +
          3 * (hyp2F1 (J τ)⁻¹ ^ 2 - 1) := by ring
    rw [hexp]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_)
    rw [norm_pow, norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
    have h0 : (0 : ℝ) ≤ ‖hyp2F1 (J τ)⁻¹ ^ 2 - 1‖ := norm_nonneg _
    nlinarith [hb2]
  have hE₆b : ‖E₆ τ - 1‖ ≤ 0.199 := norm_E₆_sub_one_le hτ
  have hE₆big : (0.8 : ℝ) < ‖E₆ τ‖ := lemE6 hτ
  have hsub : ‖hyp2F1 (J τ)⁻¹ ^ 6 - E₆ τ‖ < ‖E₆ τ‖ := by
    have h1 : hyp2F1 (J τ)⁻¹ ^ 6 - E₆ τ =
        (hyp2F1 (J τ)⁻¹ ^ 6 - 1) - (E₆ τ - 1) := by ring
    rw [h1]
    calc ‖(hyp2F1 (J τ)⁻¹ ^ 6 - 1) - (E₆ τ - 1)‖
        ≤ ‖hyp2F1 (J τ)⁻¹ ^ 6 - 1‖ + ‖E₆ τ - 1‖ := norm_sub_le _ _
      _ ≤ 0.520875 + 0.199 := add_le_add hb6 hE₆b
      _ < 0.8 := by norm_num
      _ < ‖E₆ τ‖ := hE₆big
  have hre : 0 < (hyp2F1 (J τ)⁻¹ ^ 6 / E₆ τ).re := re_div_pos_of_norm_sub_lt hsub
  -- resolve the branch of the square root
  have hbranch : (J τ / (J τ - 1)) ^ (1 / 2 : ℂ) = hyp2F1 (J τ)⁻¹ ^ 6 / E₆ τ := by
    rw [hsq, show (1 / 2 : ℂ) = ((2 : ℂ)⁻¹ : ℂ) by norm_num]
    exact Complex.sq_cpow_two_inv hre
  -- solve the E₂ identity for `E2 τ` and substitute everything
  have hE2' : E2 τ = (E₆ τ * (E₄ τ * J τ) +
      12 * hyp2F1 (J τ)⁻¹ ^ 3 * deriv hyp2F1 (J τ)⁻¹ * E₆ τ) / (E₄ τ ^ 2 * J τ) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hE₄0) hJ0)]
    exact hE2
  rw [hbranch, hderivsq, hone]
  simp only [s₂, E₂star]
  rw [hE2', hE₄]
  set g : ℂ := hyp2F1 (J τ)⁻¹ with hgdef
  set g' : ℂ := deriv hyp2F1 (J τ)⁻¹ with hg'def
  field_simp
  ring

/-- **The Main Theorem** (Milla, Thm. `hauptformel`; Chudnovsky–Chudnovsky 1988,
Eq. (1.4)): for all `τ` with `Im τ > 1.25`,
`1/(2π·Im τ)·√(J/(J−1)) = ∑ n, ((1−s₂)/6 + n)·(6n)!/((3n)!(n!)³)·(1728·J)⁻ⁿ`,
with the principal branch of the square root. -/
theorem hauptformel {τ : ℍ} (hτ : τ ∈ Region) :
    1 / (2 * (π : ℂ) * (τ.im : ℂ)) * (J τ / (J τ - 1)) ^ (1 / 2 : ℂ) =
      ∑' n : ℕ, mainSummand τ n := by
  have hJ : 1 < ‖J τ‖ := one_lt_norm_J hτ
  have hJ0 : J τ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hJ
    exact absurd hJ (by norm_num)
  have hw : ‖1 / J τ‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (lt_trans one_pos hJ)]
    exact hJ
  set w : ℂ := 1 / J τ with hwdef
  -- Summability of the two constituent series.
  have hS0 : Summable fun n : ℕ => mainCoeff n * w ^ n := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => ‖w‖ ^ n)
      (summable_geometric_of_lt_one (norm_nonneg w) hw) fun n => ?_
    rw [norm_mul, norm_pow]
    calc ‖mainCoeff n‖ * ‖w‖ ^ n ≤ 1 * ‖w‖ ^ n := by
          gcongr
          exact norm_mainCoeff_le_one n
      _ = ‖w‖ ^ n := one_mul _
  have hS1 : Summable fun n : ℕ => (n : ℂ) * (mainCoeff n * w ^ n) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) * ‖w‖ ^ n) ?_ fun n => ?_
    · have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ‖w‖)
        (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]; exact hw)
      simpa using this
    · rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      calc (n : ℝ) * (‖mainCoeff n‖ * ‖w‖ ^ n) ≤ (n : ℝ) * (1 * ‖w‖ ^ n) := by
            gcongr
            exact norm_mainCoeff_le_one n
        _ = (n : ℝ) * ‖w‖ ^ n := by ring
  rw [thm42 hτ, Gsq_eq_tsum hw, deriv_Gsq_eq hw, ← hwdef]
  -- Push the constants into the sums.
  rw [← tsum_mul_left, ← tsum_mul_left]
  have hstep : (fun n : ℕ => w * (mainCoeff n * ((n : ℂ) * w ^ (n - 1))))
      = fun n : ℕ => (n : ℂ) * (mainCoeff n * w ^ n) := by
    ext n
    rcases n with _ | k
    · simp
    · rw [Nat.succ_sub_one, pow_succ]
      push_cast
      ring
  rw [hstep]
  rw [← (hS0.mul_left ((1 - s₂ τ) / 6)).tsum_add hS1]
  refine tsum_congr fun n => ?_
  rw [mainSummand_eq hJ0 n, ← hwdef]
  ring

end Chudnovsky
