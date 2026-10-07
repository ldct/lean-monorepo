import Playground.Lagarias.BlueprintMellinCalculus

/-!
# Convergence and algebra for the defining Mellin integrals

These lemmas keep absolute integrability explicit whenever linearity is used.
Finite-cutoff transforms are proved entire by their compact support, rather
than declared to be analytic correction terms.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set Asymptotics
open scoped Topology

lemma integrableOn_truncatedMellin_of_isBigO {a r : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hloc : LocallyIntegrableOn (mellinCutoff a f) (Ioi 0))
    (htop : mellinCutoff a f =O[atTop] (fun x : ℝ => x ^ r))
    {s : ℂ} (hs : r < s.re) :
    IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-s - 1)) (Ioi a) := by
  have hm := mellinConvergent_of_isBigO_rpow
    (a := -r) (b := -s.re - 1) (s := -s) hloc
    (by simpa only [neg_neg] using htop)
    (by simp only [Complex.neg_re]; linarith)
    (mellinCutoff_isBigO_atZero ha f (-s.re - 1))
    (by simp only [Complex.neg_re]; linarith)
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * mellinCutoff a f x) (Ioi 0) at hm
  apply (hm.mono_set (Ioi_subset_Ioi ha.le)).congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [mellinCutoff, indicator_of_mem hx]
  exact mul_comm _ _

lemma integrableOn_truncatedMellin {a C r : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : Measurable f) (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r)
    {s : ℂ} (hs : r < s.re) :
    IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-s - 1)) (Ioi a) :=
  integrableOn_truncatedMellin_of_isBigO (zero_lt_one.trans_le ha)
    (locallyIntegrableOn_mellinCutoff ha hC hf hbound)
    (mellinCutoff_isBigO_atTop ha hbound) hs

set_option backward.isDefEq.respectTransparency false in
lemma hasDerivAt_truncatedMellin_of_isBigO {a r : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hloc : LocallyIntegrableOn (mellinCutoff a f) (Ioi 0))
    (htop : mellinCutoff a f =O[atTop] (fun x : ℝ => x ^ r))
    {s : ℂ} (hs : r < s.re) :
    HasDerivAt (truncatedMellin a f) (-truncatedMellin a (logWeight f) s) s := by
  have hm := mellin_hasDerivAt_of_isBigO_rpow
    (a := -r) (b := -s.re - 1) (s := -s) hloc
    (by simpa only [neg_neg] using htop)
    (by simp only [Complex.neg_re]; linarith)
    (mellinCutoff_isBigO_atZero ha f (-s.re - 1))
    (by simp only [Complex.neg_re]; linarith)
  rw [logWeight_mellinCutoff] at hm
  convert! hm.2.comp s (hasDerivAt_neg' s) using 1 <;>
    simp only [truncatedMellin, mul_neg_one]

lemma truncatedMellin_congr {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ}
    (hfg : EqOn f g (Ioi a)) (s : ℂ) : truncatedMellin a f s = truncatedMellin a g s := by
  rw [truncatedMellin_eq_integral ha, truncatedMellin_eq_integral ha]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change f x * (x : ℂ) ^ (-s - 1) = g x * (x : ℂ) ^ (-s - 1)
  rw [hfg hx]

lemma truncatedMellin_add {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ} {s : ℂ}
    (hf : IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-s - 1)) (Ioi a))
    (hg : IntegrableOn (fun x : ℝ => g x * (x : ℂ) ^ (-s - 1)) (Ioi a)) :
    truncatedMellin a (fun x => f x + g x) s = truncatedMellin a f s + truncatedMellin a g s := by
  simp only [truncatedMellin_eq_integral ha, add_mul]
  exact integral_add hf hg

lemma truncatedMellin_sub {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ} {s : ℂ}
    (hf : IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-s - 1)) (Ioi a))
    (hg : IntegrableOn (fun x : ℝ => g x * (x : ℂ) ^ (-s - 1)) (Ioi a)) :
    truncatedMellin a (fun x => f x - g x) s = truncatedMellin a f s - truncatedMellin a g s := by
  simp only [truncatedMellin_eq_integral ha, sub_mul]
  exact integral_sub hf hg

lemma truncatedMellin_ofReal {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) (v : ℝ) :
    truncatedMellin a (fun x => (f x : ℂ)) (v : ℂ) =
      ((∫ x : ℝ in Ioi a, f x * x ^ (-v - 1) : ℝ) : ℂ) := by
  rw [truncatedMellin_eq_integral ha, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 ≤ x := ha.trans (le_of_lt hx)
  change (f x : ℂ) * (x : ℂ) ^ (-(v : ℂ) - 1) = ((f x * x ^ (-v - 1) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0]
  push_cast
  rfl

/-- The upper cutoff used when subtracting a finite interval from `Q`. -/
noncomputable def upperCutoff (b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Iic b).indicator f

@[fun_prop] lemma measurable_upperCutoff {b : ℝ} {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (upperCutoff b f) := hf.indicator measurableSet_Iic

lemma upperCutoff_bound {a b C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℂ}
    (hbound : ∀ x : ℝ, a < x → x ≤ b → ‖f x‖ ≤ C) :
    ∀ x : ℝ, a < x → ‖upperCutoff b f x‖ ≤ C * x ^ (0 : ℝ) := by
  intro x hx
  rw [Real.rpow_zero, mul_one]
  by_cases hxb : x ≤ b
  · simpa [upperCutoff, hxb] using hbound x hx hxb
  · simpa [upperCutoff, hxb] using hC

lemma cutoff_isBigO_every_rpow (a b r : ℝ) (f : ℝ → ℂ) :
    mellinCutoff a (upperCutoff b f) =O[atTop] (fun x : ℝ => x ^ r) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [eventually_gt_atTop b] with x hx
  by_cases hxa : a < x <;> simp [mellinCutoff, upperCutoff, hxa, not_le_of_gt hx]

/-- The finite-cutoff correction is an entire function of its complex exponent. -/
theorem differentiable_finiteCutoffMellin {a b C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : Measurable f)
    (hbound : ∀ x : ℝ, a < x → x ≤ b → ‖f x‖ ≤ C) :
    Differentiable ℂ (truncatedMellin a (upperCutoff b f)) := by
  have hloc := locallyIntegrableOn_mellinCutoff ha hC (measurable_upperCutoff hf)
    (upperCutoff_bound hC hbound)
  intro s
  exact (hasDerivAt_truncatedMellin_of_isBigO (zero_lt_one.trans_le ha) hloc
    (cutoff_isBigO_every_rpow a b (s.re - 1) f) (by linarith)).differentiableAt

lemma finiteCutoffMellin_eq_integral {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) (s : ℂ) :
    truncatedMellin a (upperCutoff b f) s =
      ∫ x : ℝ in Ioc a b, f x * (x : ℂ) ^ (-s - 1) := by
  rw [truncatedMellin_eq_integral ha]
  calc
    _ = ∫ x : ℝ in Ioi a, (Iic b).indicator (fun x : ℝ => f x * (x : ℂ) ^ (-s - 1)) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      by_cases hxb : x ≤ b <;> simp [upperCutoff, hxb]
    _ = _ := by rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

end LeanEval.NumberTheory.Lagarias.Blueprint
