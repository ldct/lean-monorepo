# Plan: Computing ζ(3) to High Precision via Euler-Maclaurin

## Goal

Prove in Lean:
```
theorem zeta3_lo : (1.20205 : ℝ) ≤ (riemannZeta 3).re
theorem zeta3_hi : (riemannZeta 3).re ≤ 1.20206
```

## Why this is simpler than γ

The γ proof in `EulerMascheroniBounds.lean` required:
- Log inequalities (quadratic bounds, MVT chains)
- Bridging rational arithmetic with `Real.log` via `exp` lower bounds
- Taylor sum witnesses for `exp(r400)`

**For ζ(3), ALL terms are rational.** No logarithms, no π, no irrationals. The entire
computation lives in ℚ, verified by `native_decide`.

## The Euler-Maclaurin formula for ζ(3)

```
ζ(3) = Σ_{k=1}^{N-1} 1/k³ + 1/(2N²) + 1/(2N³) + Σ_{j=1}^{p} c_j / N^{2j+2}
```

where the correction coefficients are:
```
c₁ = +1/4        (from B₂)
c₂ = -1/12       (from B₄)
c₃ = +1/12       (from B₆)
c₄ = -3/20       (from B₈)
```

## Bracketing sequences

Define (all rational for integer N):
```
ζ_lo(N) := Σ_{k=1}^{N-1} 1/k³ + 1/(2N²) + 1/(2N³)                          [p=0]
ζ_hi(N) := Σ_{k=1}^{N-1} 1/k³ + 1/(2N²) + 1/(2N³) + 1/(4N⁴)               [p=1]
ζ_lo₂(N):= ζ_hi(N) - 1/(12N⁶)                                               [p=2]
ζ_hi₂(N):= ζ_lo₂(N) + 1/(12N⁸)                                              [p=3]
```

Because the Bernoulli corrections alternate in sign:
```
ζ_lo(N)  ≤ ζ(3) ≤ ζ_hi(N)       (wider bracket)
ζ_lo₂(N) ≤ ζ(3) ≤ ζ_hi₂(N)      (tighter bracket)
```

## Numerical verification

```
N=10, p=0 (lower): 1.20203198...  ≥ 1.20205? NO  — need p=2
N=10, p=2 (lower): 1.20205690...  ≥ 1.20205? YES ✓
N=10, p=1 (upper): 1.20205698...  ≤ 1.20206? YES ✓
```

So **N=10 with 2 correction terms** suffices for 5 decimal places.

## Proof structure (6 steps)

### Step 1: Connect `riemannZeta 3` to a real-valued tsum

Use Mathlib's `zeta_nat_eq_tsum_of_gt_one` (for ℂ) and extract the real part:
```
riemannZeta 3 = ∑' n, 1/(n:ℂ)^3
```
Then show `(riemannZeta 3).re = ∑' n, 1/(n:ℝ)^3` (since all terms are real).

Key Mathlib lemmas:
- `zeta_nat_eq_tsum_of_gt_one` (ℂ-valued sum = ζ)
- `riemannZeta_pos_of_one_lt` (real and positive for re > 1)

### Step 2: Split tsum into partial sum + tail

```
∑' n, 1/(n+1)^3 = Σ_{k=0}^{N-2} 1/(k+1)^3 + ∑'_{k≥N-1} 1/(k+1)^3
                 = Σ_{k=1}^{N-1} 1/k^3 + Σ_{k=N}^∞ 1/k^3
```

Key Mathlib lemma: `tsum_eq_zero_add` / `sum_add_tsum_compl`

### Step 3: Bound the tail with integrals (the E-M core)

**Lower bound on tail** (tail ≥ integral):
```
Σ_{k=N}^∞ 1/k³ ≥ ∫_N^∞ 1/x³ dx + ½·1/N³ = 1/(2N²) + 1/(2N³)
```
This follows because 1/x³ is convex, so the sum (left Riemann sum of a
decreasing function starting at the left endpoint) exceeds the integral.
More precisely: for convex decreasing f, f(k) ≥ ∫_k^{k+1} f(x) dx + ½(f(k)-f(k+1))
by the trapezoidal rule being an overestimate for convex functions.

**Upper bound on tail** (add first Bernoulli correction):
```
Σ_{k=N}^∞ 1/k³ ≤ 1/(2N²) + 1/(2N³) + 1/(4N⁴)
```
This is the integral + endpoint + B₂ correction, which overshoots because
the next (B₄) correction is negative.

### Step 4: Prove the alternating bound property

The key analytical lemma: for f(x) = 1/x³, the Euler-Maclaurin remainder
after p terms has sign (-1)^p. This follows from f^{(2p+1)}(x) having
constant sign on (0,∞) for each p (since all derivatives of 1/x³ are
monotone on (0,∞)).

**Proof approach** (following the γ file's style):

For the LOWER bound (p=0), we need:
```
∀ k ≥ N, 1/k³ ≥ ∫_k^{k+1} 1/x³ dx + 1/(2k³) - 1/(2(k+1)³)
                  ... (telescopes to give integral + endpoint correction)
```
This reduces to showing `1/k³ - log-free integral bound`, which for 1/x³
becomes `1/k³ ≥ 1/(2k²) - 1/(2(k+1)²)`, i.e., a rational inequality.

Actually, the cleanest approach: **directly bound the tail sum vs integral**.

For convex decreasing f on [N,∞):
- Lower: Σ_{k=N}^∞ f(k) ≥ ∫_N^∞ f(x)dx + ½f(N)   [trapezoidal ≥ integral for convex]
- Upper: Σ_{k=N}^∞ f(k) ≤ ∫_N^∞ f(x)dx + ½f(N) + (1/12)f'(N)   [next E-M correction]

For f(x) = x^{-3}: f is convex on (0,∞), ∫_N^∞ = 1/(2N²), ½f(N) = 1/(2N³),
f'(N) = -3/N⁴, so (1/12)f'(N) = -1/(4N⁴).

Wait — that gives the WRONG sign for the upper bound. Let me re-examine...

Actually the standard E-M tail formula is:
```
Σ_{k=N}^∞ f(k) = ∫_N^∞ f(x)dx + ½f(N) - Σ_{j=1}^p B_{2j}/(2j)! f^{(2j-1)}(N) + R_p
```
Note the MINUS sign. For f(x) = x^{-3}:
- f'(N) = -3N^{-4}, so -B₂/2!·f'(N) = -(1/12)·(-3/N⁴) = +1/(4N⁴)  ✓

This gives ζ_hi correctly. The alternation of the remainder R_p gives the bounds.

### Step 5: Computational verification (all rational — `native_decide`)

Define in ℚ:
```
def ζ_lo_q : ℚ := (Finset.range 9).sum (fun k => 1/(k+1)^3) + 1/(2·10^2) + 1/(2·10^3)
def ζ_hi_q : ℚ := ζ_lo_q + 1/(4·10^4)
```

Verify:
```
lemma ζ_lo_ge : ζ_lo_q ≥ 120205/100000 := by native_decide   -- 1.20205
lemma ζ_hi_le : ζ_hi_q ≤ 120206/100000 := by native_decide   -- 1.20206
```

### Step 6: Assemble the final theorem

```
theorem zeta3_bounds : 1.20205 ≤ (riemannZeta 3).re ∧ (riemannZeta 3).re ≤ 1.20206 := by
  constructor
  · calc 1.20205 = (120205 : ℚ)/100000 := ...
       _ ≤ ζ_lo_q := ζ_lo_ge
       _ ≤ (riemannZeta 3).re := em_lower_bound ...
  · calc (riemannZeta 3).re ≤ ζ_hi_q := em_upper_bound ...
       _ ≤ 1.20206 := ζ_hi_le
```

## Comparison with the γ proof

| Aspect | γ bounds | ζ(3) bounds |
|--------|----------|-------------|
| Computation domain | ℚ + ℝ (need log) | **Pure ℚ** |
| Hardest analytical step | Chain of 3 MVT inequalities for log | Convexity of 1/x³ |
| Numerical witness | exp(r400) > 401 via Taylor | **Simple ℚ comparison** |
| native_decide complexity | Taylor sum of 23 terms | Partial sum of 9 terms |
| Required Mathlib API | `eulerMascheroniSeq`, `tendsto_harmonic_sub_log` | `riemannZeta`, `zeta_nat_eq_tsum_of_gt_one` |

## Key difficulty / risk

The main risk is **Step 3**: Mathlib may not have a ready-made "Euler-Maclaurin remainder
bound for tails of decreasing convex functions." We may need to prove from scratch:

> For f convex and decreasing on [N,∞) with f(x) → 0:
> ∫_N^∞ f(x)dx + ½f(N) ≤ Σ_{k=N}^∞ f(k)

This is the "trapezoidal rule overestimates for convex functions" result.
For the upper bound we additionally need the first Bernoulli correction.

**Fallback**: If E-M machinery is too heavy, use direct comparison:
```
Σ_{k=N}^∞ 1/k³ ≥ ∫_N^∞ 1/x³ dx = 1/(2N²)           [integral test, easy]
Σ_{k=N}^∞ 1/k³ ≤ 1/N³ + ∫_N^∞ 1/x³ dx = 1/N³ + 1/(2N²)   [also easy]
```
This gives a cruder bound but avoids E-M entirely. With N=100 or so,
it still gives enough precision for 4-5 digits.
