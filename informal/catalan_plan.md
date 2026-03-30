# Plan: Bounds on Catalan's Constant via Euler-Maclaurin

## Goal

Prove in Lean:
```lean
theorem catalan_lo : (9159 : ℝ) / 10000 ≤ catalanConstant
theorem catalan_hi : catalanConstant ≤ (9161 : ℝ) / 10000
```

(That is, `0.9159 ≤ G ≤ 0.9161`, capturing the true value G ≈ 0.9159655941…)

## What is Catalan's constant?

Catalan's constant is the alternating series:

$$G = \sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^2} = 1 - \frac{1}{9} + \frac{1}{25} - \frac{1}{49} + \cdots$$

Mathlib does **not** have a definition of Catalan's constant (as of v4.28.0).

## Key idea: split into positive and negative parts

Group even-index (positive) and odd-index (negative) terms:

$$G = \underbrace{\sum_{k=0}^{\infty} \frac{1}{(4k+1)^2}}_{P} - \underbrace{\sum_{k=0}^{\infty} \frac{1}{(4k+3)^2}}_{Q}$$

Both P and Q are monotone positive series with terms of the form `1/(4k+a)²`.
We apply Euler-Maclaurin-style integral comparison bounds to each separately.

## Bounding sequences

For a series $S(a) = \sum_{k=0}^{\infty} 1/(4k+a)^2$ with $a \in \{1, 3\}$:

### Lower bound (increasing)
$$S_{\text{lo}}(a, N) = \sum_{k=0}^{N-1} \frac{1}{(4k+a)^2} + \frac{1}{4(4N+a)} + \frac{1}{2(4N+a)^2}$$

- First N−1 computed terms
- Plus tail integral: $\int_N^\infty 1/(4x+a)^2\,dx = 1/(4(4N+a))$
- Plus trapezoidal correction: $f(N)/2 = 1/(2(4N+a)^2)$

### Upper bound (decreasing)
$$S_{\text{hi}}(a, N) = \sum_{k=0}^{N} \frac{1}{(4k+a)^2} + \frac{1}{4(4N+a)}$$

- First N+1 computed terms (through index N)
- Plus tail integral: $\int_N^\infty 1/(4x+a)^2\,dx = 1/(4(4N+a))$

### Catalan bounds
$$G_{\text{lo}}(N) = S_{\text{lo}}(1, N) - S_{\text{hi}}(3, N) \leq G \leq S_{\text{hi}}(1, N) - S_{\text{lo}}(3, N) = G_{\text{hi}}(N)$$

## Step identities (the analytical core)

These are **the same for both a=1 and a=3** — they depend only on x = 4N+a.

Let $x > 0$:

### Lower bound step (fraction identity)
$$\frac{1}{x^2} + \frac{1}{4(x+4)} + \frac{1}{2(x+4)^2} - \frac{1}{4x} - \frac{1}{2x^2} = \frac{8}{x^2(x+4)^2}$$

This gives:
$$S_{\text{lo}}(a, N+1) - S_{\text{lo}}(a, N) = \frac{8}{(4N+a)^2(4N+a+4)^2} > 0$$

### Upper bound step (fraction identity)
$$\frac{1}{(x+4)^2} + \frac{1}{4(x+4)} - \frac{1}{4x} = \frac{-4}{x(x+4)^2}$$

This gives:
$$S_{\text{hi}}(a, N+1) - S_{\text{hi}}(a, N) = \frac{-4}{(4N+a)(4N+a+4)^2} < 0$$

### Derivation of lo step
Combine over common denominator $2x^2(x+4)^2$:
$$\frac{(x+4)^2 + a^2 - 2x(x+4)}{2x^2(x+4)^2}$$

Numerator: $(x+4)^2 + x^2 - 2x(x+4) = (x+4-x)^2 = 16$.
So result is $16/(2x^2(x+4)^2) = 8/(x^2(x+4)^2)$.

### Derivation of hi step
Combine over common denominator $4x(x+4)^2$:
Numerator: $4x + x(x+4) - (x+4)^2 = 4x + x^2 + 4x - x^2 - 8x - 16 = -16$.
So result is $-16/(4x(x+4)^2) = -4/(x(x+4)^2)$.

## Numerical evaluation at N = 23

| Quantity | Value |
|----------|-------|
| S_lo(1, 23) | 1.074832243644 |
| S_hi(1, 23) | 1.074890053795 |
| S_lo(3, 23) | 0.158866700688 |
| S_hi(3, 23) | 0.158922102350 |
| G_lo = S_lo(1,23) − S_hi(3,23) | 0.915910141294 ≥ 0.9159 ✓ |
| G_hi = S_hi(1,23) − S_lo(3,23) | 0.916023353107 ≤ 0.9161 ✓ |

## File structure: `CatalanBounds.lean`

### Section 1: Summability and Tendsto

```lean
-- Summability by comparison with ∑ 1/(k+1)²
summable_inv_sq_arith (a : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ => 1 / ((4 * ↑k + ↑a : ℝ))^2)

-- Tendsto of partial sums to tsum
tendsto_partial_sum (a : ℕ) (ha : 0 < a) :
    Tendsto (fun N => ∑ k in range N, 1 / ((4*↑k+↑a : ℝ))^2)
      atTop (𝓝 (∑' k, 1 / ((4*↑k+↑a : ℝ))^2))
```

### Section 2: Bounding sequence definitions

```lean
def S_lo (a N : ℕ) : ℝ :=
  (range (N-1)).sum (fun k => 1/((4*↑k+↑a : ℝ))^2) +
    1/(4*(4*↑N+↑a)) + 1/(2*(4*↑N+↑a)^2)

def S_hi (a N : ℕ) : ℝ :=
  (range N).sum (fun k => 1/((4*↑k+↑a : ℝ))^2) +
    1/(4*(4*↑N+↑a))
```

### Section 3: Fraction identities

Two fraction identities, proved by `eq_div_iff` + manual clearing:

```lean
lo_frac_identity (x : ℝ) (hx : x > 0) :
    1/x^2 + 1/(4*(x+4)) + 1/(2*(x+4)^2) - 1/(4*x) - 1/(2*x^2) =
    8 / (x^2 * (x+4)^2)

hi_frac_identity (x : ℝ) (hx : x > 0) :
    1/(x+4)^2 + 1/(4*(x+4)) - 1/(4*x) =
    -4 / (x * (x+4)^2)
```

### Section 4: Step identities

```lean
S_lo_step (a N : ℕ) (ha : 0 < a) (hN : 1 ≤ N) :
    S_lo a (N+1) - S_lo a N = 8 / ((4*↑N+↑a)^2 * (4*↑N+↑a+4)^2)

S_hi_step (a N : ℕ) (ha : 0 < a) (hN : 1 ≤ N) :
    S_hi a (N+1) - S_hi a N = -4 / ((4*↑N+↑a) * (4*↑N+↑a+4)^2)
```

### Section 5: Monotonicity (from step signs)

```lean
S_lo_mono (a : ℕ) (ha : 0 < a) : Monotone (fun N => S_lo a (N + 1))
S_hi_anti (a : ℕ) (ha : 0 < a) : Antitone (fun N => S_hi a (N + 1))
```

### Section 6: Convergence of bounds to tsum

```lean
tendsto_S_lo (a : ℕ) (ha : 0 < a) :
    Tendsto (S_lo a) atTop (𝓝 (∑' k, 1/((4*↑k+↑a : ℝ))^2))

tendsto_S_hi (a : ℕ) (ha : 0 < a) :
    Tendsto (S_hi a) atTop (𝓝 (∑' k, 1/((4*↑k+↑a : ℝ))^2))
```

### Section 7: Bounds on tsum

```lean
S_lo_le (a N : ℕ) (ha : 0 < a) (hN : 1 ≤ N) :
    S_lo a N ≤ ∑' k, 1/((4*↑k+↑a : ℝ))^2

le_S_hi (a N : ℕ) (ha : 0 < a) (hN : 1 ≤ N) :
    ∑' k, 1/((4*↑k+↑a : ℝ))^2 ≤ S_hi a N
```

### Section 8: Catalan definition and final bounds

```lean
noncomputable def catalanConstant : ℝ :=
  (∑' k, 1/((4*↑k+1 : ℝ))^2) - (∑' k, 1/((4*↑k+3 : ℝ))^2)

-- Rational approximation definitions for norm_num
def G_lo_q : ℚ := ...
def G_hi_q : ℚ := ...

-- Numerical checks
lemma G_lo_q_ge : G_lo_q ≥ 9159/10000 := by norm_num [...]
lemma G_hi_q_le : G_hi_q ≤ 9161/10000 := by norm_num [...]

-- Cast to ℝ
lemma G_lo_q_cast : (G_lo_q : ℝ) = S_lo 1 23 - S_hi 3 23 := by norm_num [...]
lemma G_hi_q_cast : (G_hi_q : ℝ) = S_hi 1 23 - S_lo 3 23 := by norm_num [...]

-- Final theorems
theorem catalan_lo : (9159 : ℝ) / 10000 ≤ catalanConstant
theorem catalan_hi : catalanConstant ≤ (9161 : ℝ) / 10000
```

## Comparison with PiSqBounds / Zeta3Bounds

| Aspect | ζ(2)/π² | ζ(3) | Catalan |
|--------|---------|------|---------|
| Series | ∑ 1/k² | ∑ 1/k³ | ∑ 1/(4k+1)² − ∑ 1/(4k+3)² |
| Mathlib anchor | `hasSum_zeta_two` | `riemannZeta` + cpow | None (define from scratch) |
| Bounding seqs | 2 (lo, hi) | 2 (lo, hi) | 4 (P_lo, P_hi, Q_lo, Q_hi) |
| Fraction identities | 2 | 2 | 2 (shared between P and Q) |
| N for evaluation | 23 | 23 | 23 |
| Precision | 3 dp of π² | 4 dp of ζ(3) | 3-4 dp of G |

## Key differences from previous files

1. **No Mathlib anchor**: We define `catalanConstant` ourselves as `P - Q`.
   No need to connect to `riemannZeta` or `hasSum_zeta_two`.

2. **Two series**: We bound P and Q separately, then combine.
   This doubles the bound arguments but the fraction identities are shared.

3. **Shift is 4, not 1**: In ζ(p), consecutive terms differ by 1 in the base.
   Here consecutive terms differ by 4 (since 4(k+1)+a = (4k+a) + 4).
   So the fraction identities use `x+4` instead of `x+1`.

4. **Summability from scratch**: Must prove `Summable (fun k => 1/(4k+a)²)`
   by comparison with `∑ 1/(k+1)²` which is summable by `summable_one_div_nat_pow`.

## Potential difficulties

- **nat cast arithmetic**: `4 * ↑k + ↑a` vs `↑(4*k+a)` — need to be consistent.
  Probably work with `(4 * (k : ℝ) + (a : ℝ))` throughout.

- **`field_simp; ring` is broken**: Same as in PiSqBounds/Zeta3Bounds.
  Use `eq_div_iff` + manual `inv_mul_cancel_left₀` clearing.

- **norm_num on large rational sums**: With N=23, each sum has 23-24 terms.
  Need `set_option maxHeartbeats 4000000`. May need 8000000 since we have
  4 sums (P_lo partial, P_hi partial, Q_lo partial, Q_hi partial).
  But can split into separate `norm_num` calls.

- **Monotone/Antitone indexing**: The shifted indexing `fun N => S_lo a (N+1)`
  is needed because `S_lo a 0` is degenerate (range (0-1) = range 0 = ∅ in ℕ).

## Estimated size

~400-500 lines (PiSqBounds is ~350 lines, and this has two series but shared identities).
