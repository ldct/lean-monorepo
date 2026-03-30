# Plan: Computing ζ(3) to High Precision via Euler-Maclaurin

## Goal

Prove in Lean:
```
theorem zeta3_lo : (1.2020 : ℝ) ≤ (riemannZeta 3).re
theorem zeta3_hi : (riemannZeta 3).re ≤ 1.2021
```

(4 decimal places. Achievable at N=23 with the simple approach below.)

## Key insight: much simpler than γ

The γ proof needed log inequalities (quadratic bounds, 3-step MVT chain, Taylor
witnesses for exp). **For ζ(3), everything is rational.** The entire proof reduces
to two trivial polynomial inequalities + a `native_decide` check.

## The two sequences

```
ζ_lo(N) := Σ_{k=1}^{N-1} 1/k³ + 1/(2N²) + 1/(2N³)    (lower bound)
ζ_hi(N) := Σ_{k=1}^{N}   1/k³ + 1/(2N²)               (upper bound)
```

Both are rational for integer N. No logs, no π, no irrationals.

## Step 1: Monotonicity (the analytical core)

**ζ_lo is increasing:**
```
ζ_lo(N+1) - ζ_lo(N) = (2N + 1) / (2N³(N+1)³)  >  0
```

**ζ_hi is decreasing:**
```
ζ_hi(N+1) - ζ_hi(N) = -(3N + 1) / (2N²(N+1)³)  <  0
```

Both are single-line polynomial identities, provable by `field_simp; ring` or
`nlinarith` after clearing denominators. Compare: the γ lower bound required
proving `log(1+x) ≤ x(2+x)/(2(1+x))` via an exponential bound, then 3 chained
MVT arguments.

### Derivation

For ζ_lo, combine over common denominator 2N³(N+1)³:
```
  numerator = 2(N+1)³ + N³(N+1) + N³ - N(N+1)³ - (N+1)³
            = 2N + 1
```

For ζ_hi, combine over common denominator 2N²(N+1)³:
```
  numerator = 2N² + N²(N+1) - (N+1)³
            = -(3N + 1)
```

## Step 2: Convergence

**ζ_lo(N) → ζ(3):**
```
ζ_lo(N) = [Σ_{k=1}^{N-1} 1/k³] + 1/(2N²) + 1/(2N³)
```
The partial sum → ζ(3), and the corrections → 0.

**ζ_hi(N) → ζ(3):**
```
ζ_hi(N) = [Σ_{k=1}^{N} 1/k³] + 1/(2N²)
```
Same argument.

Key Mathlib lemma: `zeta_nat_eq_tsum_of_gt_one` gives
`riemannZeta 3 = ∑' n, 1/(n:ℂ)^3`, and summability gives
`∑' n, 1/(n+1:ℝ)^3 = lim Σ_{k=1}^{N} 1/k³`.

## Step 3: Therefore

Increasing + converges to L ⟹ bounded above by L:
```
∀ N, ζ_lo(N) ≤ ζ(3)       (since ζ_lo ↑ ζ(3))
∀ N, ζ(3) ≤ ζ_hi(N)       (since ζ_hi ↓ ζ(3))
```

This is the same pattern as the γ file's `eulerMascheroniConstant_lb` and
`euler_maclaurin_bound`.

## Step 4: Numerical evaluation (N = 23)

```lean
def ζ_lo_q : ℚ := (Finset.range 22).sum (fun k => 1/(k+1)^3) + 1/(2*23^2) + 1/(2*23^3)
def ζ_hi_q : ℚ := (Finset.range 23).sum (fun k => 1/(k+1)^3) + 1/(2*23^2)

lemma ζ_lo_ge : ζ_lo_q ≥ 12020/10000 := by native_decide
lemma ζ_hi_le : ζ_hi_q ≤ 12021/10000 := by native_decide
```

Numerical values:
- ζ_lo(23) = 1.20205601... ≥ 1.2020 ✓
- ζ_hi(23) = 1.20209710... ≤ 1.2021 ✓

## Full proof outline

```lean
-- 1. Connect riemannZeta to real-valued tsum
lemma zeta3_eq_tsum : (riemannZeta 3).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

-- 2. Define the sequences (ℝ-valued)
noncomputable def ζ_lo (N : ℕ) : ℝ :=
  (Finset.range (N-1)).sum (fun k => 1/((k:ℝ)+1)^3) + 1/(2*N^2) + 1/(2*N^3)

noncomputable def ζ_hi (N : ℕ) : ℝ :=
  (Finset.range N).sum (fun k => 1/((k:ℝ)+1)^3) + 1/(2*N^2)

-- 3. Step bounds (the only analytical content)
lemma ζ_lo_step (N : ℕ) (hN : 1 ≤ N) :
    ζ_lo (N+1) - ζ_lo N = (2*N+1) / (2*N^3*(N+1)^3) := by
  field_simp; ring

lemma ζ_hi_step (N : ℕ) (hN : 1 ≤ N) :
    ζ_hi (N+1) - ζ_hi N = -(3*N+1) / (2*N^2*(N+1)^3) := by
  field_simp; ring

-- 4. Monotonicity (immediate from step signs)
lemma ζ_lo_strictMono : StrictMono (fun N => ζ_lo (N+1))  -- from step > 0
lemma ζ_hi_strictAnti : StrictAnti (fun N => ζ_hi (N+1))  -- from step < 0

-- 5. Convergence
lemma ζ_lo_tendsto : Tendsto ζ_lo atTop (nhds (riemannZeta 3).re)
lemma ζ_hi_tendsto : Tendsto ζ_hi atTop (nhds (riemannZeta 3).re)

-- 6. Bounds (monotone + limit)
lemma ζ_lo_le : ∀ N, 1 ≤ N → ζ_lo N ≤ (riemannZeta 3).re
lemma ζ_hi_ge : ∀ N, 1 ≤ N → (riemannZeta 3).re ≤ ζ_hi N

-- 7. Computational verification
lemma ζ_lo_23_ge : (12020 : ℝ) / 10000 ≤ ζ_lo 23  -- via native_decide on ℚ
lemma ζ_hi_23_le : ζ_hi 23 ≤ (12021 : ℝ) / 10000  -- via native_decide on ℚ

-- 8. Final theorems
theorem zeta3_lo : (1.2020 : ℝ) ≤ (riemannZeta 3).re :=
  calc 1.2020 = 12020/10000 := by norm_num
    _ ≤ ζ_lo 23 := ζ_lo_23_ge
    _ ≤ (riemannZeta 3).re := ζ_lo_le 23 (by norm_num)

theorem zeta3_hi : (riemannZeta 3).re ≤ 1.2021 :=
  calc (riemannZeta 3).re ≤ ζ_hi 23 := ζ_hi_ge 23 (by norm_num)
    _ ≤ 12021/10000 := ζ_hi_23_le
    _ = 1.2021 := by norm_num
```

## Comparison with γ proof

| Aspect | γ bounds | ζ(3) bounds |
|--------|----------|-------------|
| Analytical core | 3-step MVT chain for log | **2N+1 > 0 and 3N+1 > 0** |
| Computation domain | ℚ + ℝ (need log, exp) | **Pure ℚ** |
| Numerical witness | 23-term Taylor sum for exp(r400) | **ℚ comparison** |
| native_decide | Taylor sum > 401 | Partial sum comparison |
| N required | N=400 (lower), N=16 (upper) | **N=23 (both)** |
| Hardest Lean step | `one_add_le_exp_quadratic_div` | `field_simp; ring` |

## Risks

1. **Connecting `riemannZeta 3` to a real tsum**: The Mathlib `riemannZeta` is ℂ-valued.
   We need `zeta_nat_eq_tsum_of_gt_one` plus `Complex.ofReal` reasoning to extract the
   real part. This is the most annoying part, but it's just API wrangling, not math.

2. **Convergence proof**: Showing `ζ_lo → ζ(3)` requires showing
   `Σ_{k=1}^{N-1} 1/k³ → ∑' 1/k³` and `1/(2N²) + 1/(2N³) → 0`. Both are standard
   with `hasSum_iff_tendsto_nat_of_nonneg` and `tendsto_const_div_atTop_nhds_zero_nat`.

3. **native_decide speed**: N=23 means summing 22 rational cubes. Should be fast.
