# Ideas for Proving Bounds on Constants in Lean

Each entry describes a constant, the proof strategy (following the monotone
sequence + `native_decide` pattern from the γ and ζ(3) proofs), and a
difficulty estimate relative to those proofs.

---

## 1. ln(2) via the alternating harmonic series

**Target:**
```lean
theorem ln2_lo : (0.6931471 : ℝ) ≤ Real.log 2
theorem ln2_hi : Real.log 2 ≤ 0.6931472
```

**Strategy:** The alternating harmonic series gives:
```
ln(2) = 1 - 1/2 + 1/3 - 1/4 + ...
```
Partial sums alternate above and below ln(2):
```
S_{2n}   = Σ_{k=1}^{2n} (-1)^{k+1}/k  ≤  ln(2)  ≤  S_{2n+1}
```

Both sequences are rational. Monotonicity is trivial:
- S_{2n+2} - S_{2n} = 1/(2n+1) - 1/(2n+2) = 1/((2n+1)(2n+2)) > 0
- S_{2n+3} - S_{2n+1} = -1/(2n+2) + 1/(2n+3) < 0

Convergence: standard alternating series test (in Mathlib?).

**Difficulty: Easy.** Almost identical structure to ζ(3). No irrationals
in the computation. The alternating series lemma does all the work.

**Needed N:** Slow convergence (error ~ 1/(2N)). For 7 digits, need N ≈ 5×10⁶.

**Better approach:** Use the faster series
```
ln(2) = Σ_{k=1}^∞ 1/(k · 2^k)
```
All terms positive, partial sums increase to ln(2). The tail is bounded by
a geometric series: Σ_{k=N+1}^∞ 1/(k·2^k) ≤ 1/((N+1)·2^N). With N=30,
this gives ~9 digits. Everything rational.

**Even better:** Use the identity `ln(2) = ln(4/3) + ln(3/2)` with the
series `ln(1+x) = x - x²/2 + x³/3 - ...` at x=1/3 and x=1/2.
Both converge geometrically. N=20 gives 10+ digits.

**Connection:** The γ proof already uses `Real.log_two_gt_d9` for log 2
bounds. This would provide a self-contained proof of that lemma.

---

## 2. π via ζ(2) = π²/6

**Target:**
```lean
theorem pi_lo : (3.14159265 : ℝ) ≤ Real.pi
theorem pi_hi : Real.pi ≤ 3.14159266
```

**Strategy:** Mathlib knows `ζ(2) = π²/6` (via `hasSum_zeta_nat` or
`riemannZeta_two_mul_nat`). So:
1. Prove `a ≤ ζ(2) ≤ b` using the same monotone sequence approach as ζ(3)
2. Then `6a ≤ π² ≤ 6b`
3. Then `√(6a) ≤ π ≤ √(6b)` (needs `Real.sqrt_le_sqrt`)
4. Bound `√(6a)` and `√(6b)` using rational approximations to √

For step 4, use: if `p²/q² ≤ 6a` then `p/q ≤ √(6a) ≤ π`. This is
a purely rational check.

**The ζ(2) bounds are easier than ζ(3)** since we can also verify against
the known identity π²/6. The monotone sequence approach is identical.

**Difficulty: Medium.** The ζ(2) part is easy (copy ζ(3) proof). The
square root extraction step adds complexity but is conceptually simple.

**Needed N:** Same as ζ(3). N=23 gives 4 decimal places of ζ(2), hence
~2 decimal places of π (since √ halves precision). For 8 digits of π,
need ~16 digits of ζ(2), which needs N ≈ 10⁴ or E-M corrections.

**Alternative:** Use the Machin-like formula
`π/4 = 4·arctan(1/5) - arctan(1/239)` with Taylor series for arctan.
Converges much faster. All rational.

---

## 3. Catalan's constant G = L(2, χ₄)

**Target:**
```lean
theorem catalan_lo : (0.9159655 : ℝ) ≤ catalan
theorem catalan_hi : catalan ≤ 0.9159656
```

**Strategy:** Catalan's constant is:
```
G = 1 - 1/3² + 1/5² - 1/7² + ... = Σ_{k=0}^∞ (-1)^k / (2k+1)²
```

This is an alternating series of decreasing terms. Same pattern:
```
S_{2n}   ≤ G ≤ S_{2n+1}
```

Partial sums are rational. Monotonicity is trivial (alternating, decreasing).

**Difficulty: Easy.** Essentially the same as ln(2) via alternating series.
The only question is whether Mathlib has a definition of Catalan's constant
or if we define it as this series.

**Connection:** G = L(2, χ₄) where χ₄ is the Dirichlet character mod 4.
This directly relates to the Dirichlet L-function application from our
discussion, and to the PNT in arithmetic progressions.

**Needed N:** Error ~ 1/(2N+1)². For 7 digits, need N ≈ 2200. Reasonable
for `native_decide`.

---

## 4. Stirling bounds: n! ≈ √(2πn) · (n/e)^n

**Target:**
```lean
theorem stirling_lb (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n ≤ n ! * Real.exp (1/(12*n))

theorem stirling_ub (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)! ≤ Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n * Real.exp (1/(12*n))
```

Or more simply, just bound `log(n!)`:
```lean
theorem log_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    n * log n - n + log(2*π*n)/2 ≤ log (n !)
    ∧ log (n !) ≤ n * log n - n + log(2*π*n)/2 + 1/(12*n)
```

**Strategy:** This IS Euler-Maclaurin applied to f(x) = log(x), which was
application #1 from our discussion. Define:
```
S_lo(n) = Σ_{k=1}^{n} log(k) - ∫₁ⁿ log(x) dx - ½ log(n)
S_hi(n) = S_lo(n) + 1/(12n)
```

Show S_lo is increasing, S_hi is decreasing, both converge.

**Difficulty: Hard.** This involves log, so it has the same complications as
the γ proof. The step bounds require showing convexity of log, which needs
the same MVT-style arguments. Not harder than γ, but not simpler either.

**Significance:** Stirling's formula is one of the most useful asymptotic
results in all of mathematics. Having formal bounds would be very valuable.

---

## 5. e (Euler's number) via Taylor series

**Target:**
```lean
theorem e_lo : (2.718281828 : ℝ) ≤ Real.exp 1
theorem e_hi : Real.exp 1 ≤ 2.718281829
```

**Strategy:** The Taylor series for exp is:
```
e = Σ_{k=0}^∞ 1/k!
```

All terms positive, so partial sums give lower bounds:
```
Σ_{k=0}^{N} 1/k!  ≤  e
```

For the upper bound, the tail is:
```
Σ_{k=N+1}^∞ 1/k! ≤ 1/(N+1)! · Σ_{j=0}^∞ 1/(N+1)^j = 1/(N+1)! · (N+1)/N
                   = 1/(N · N!)
```

So `e ≤ Σ_{k=0}^{N} 1/k! + 1/(N·N!)`. Both bounds are rational.

**Difficulty: Very Easy.** This might be the simplest of all. The partial
sums are trivially increasing (adding positive terms). The tail bound is a
geometric series comparison. Mathlib already has `Real.sum_le_exp_of_nonneg`.

**Needed N:** For 9 digits, N ≈ 13 suffices (13! ≈ 6×10⁹).

**Connection:** The γ proof already uses `exp` bounds internally. This would
provide the foundation for those bounds.

---

## 6. 1/π via Ramanujan-type series (stretch goal)

**Target:**
```lean
theorem pi_inv_bounds : |1/π - 12/√(640320³) * Σ_{k=0}^{1} ...| < 10⁻³⁰
```

**Strategy:** The Chudnovsky series:
```
1/π = 12 · Σ_{k=0}^∞ (-1)^k (6k)! (545140134k + 13591409) / ((3k)! (k!)³ 640320^{3k+3/2})
```

Each term gives about 14 new digits. ONE term gives π to 14 digits.

**Difficulty: Very Hard.** The series itself is rational except for the
√640320³ factor. Proving it equals 1/π requires deep modular form theory
that is almost certainly not in Mathlib. But we could DEFINE a sequence
and prove it's monotone + converges, if the identity is taken as an axiom
or proved separately.

**Significance:** Would be a landmark formalization result.

---

## 7. The Casimir energy: ζ(-1) = -1/12 (regularized)

**Target:**
```lean
theorem zeta_neg_one : riemannZeta (-1) = -1/12
```

**Strategy:** Mathlib already has `riemannZeta_neg_nat_eq_bernoulli`:
```
ζ(-n) = (-1)^n · B_{n+1} / (n+1)
```
So ζ(-1) = -B₂/2 = -1/12.

**Difficulty: Trivial** (if the Mathlib lemma exists). Just unfold and compute.

**Connection:** This is the Casimir effect application — the "-1/12" that gives
the attractive force between conducting plates.

---

## 8. Bounds on the Barnes G-function: log G(n)

**Target:**
```lean
theorem barnes_g_bound (n : ℕ) (hn : 10 ≤ n) :
    |log (barnesG n) - (n^2/2 * log n - 3*n^2/4 + n/2 * log(2*π) - log(n)/12 + ζ'(-1))| 
    ≤ 1/(12*n)
```

**Strategy:** The Kinkelin asymptotic formula. Define:
```
log G(n+1) = Σ_{k=1}^{n-1} log(k!)
```

Use Stirling on each log(k!) term, or apply E-M directly to f(x) = log Γ(x).

**Difficulty: Very Hard.** Requires Stirling (which requires log bounds),
plus the definition of ζ'(-1). This is a research-level formalization.

**Connection:** Barnes G-function application #4 from our discussion.

---

## 9. Lattice point bounds: the Gauss circle problem

**Target:**
```lean
theorem gauss_circle (r : ℕ) (hr : 1 ≤ r) :
    |#{(x,y) : ℤ×ℤ | x^2 + y^2 ≤ r^2} - π * r^2| ≤ C * r^(2/3)
```

**Strategy:** This is a consequence of E-M applied to characteristic
functions / Poisson summation. The bound `O(r^{2/3})` is due to
Huxley (2003) and is extremely deep.

A more tractable version: just prove the volume bound
```
|#lattice points - π r²| ≤ 3r    (for r ≥ 1)
```
which follows from the simple geometric argument that each lattice point
corresponds to a unit square, and boundary squares contribute O(r).

**Difficulty: Medium** (for the O(r) bound). **Impossible** (for O(r^{2/3})).

**Connection:** Lattice point counting application #3 from our discussion.

---

## 10. Trapezoidal rule error bounds

**Target:**
```lean
theorem trapezoidal_error (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) 
    (hf : ∀ x ∈ Set.Icc a b, ‖deriv (deriv f) x‖ ≤ M) :
    |∫ x in a..b, f x - trapezoidal_sum f a b n| ≤ M * (b-a)^3 / (12 * n^2)
```

**Strategy:** The classical error bound `|E_T| ≤ M₂(b-a)³/(12n²)` is a
direct consequence of Euler-Maclaurin with p=0:
```
∫f - Trap = -B₂/2! · h² · (f'(b) - f'(a)) + O(h⁴)
```

For convex f, the trapezoidal rule OVERESTIMATES (no absolute values needed).

**Difficulty: Medium.** The bound itself is a standard calculus result.
The Lean formalization requires integration API and derivative bounds.
Mathlib likely has pieces of this.

**Connection:** Application #1 — "why the trapezoidal rule is magically good."
This would be the formal version of that story.

---

## Difficulty ranking

| Constant | Difficulty | N needed | Key challenge |
|----------|-----------|----------|---------------|
| e | Very Easy | 13 | Geometric tail bound |
| ζ(-1) = -1/12 | Trivial | 0 | Just unfold Mathlib |
| ln(2) | Easy | 30 (fast series) | Alternating series |
| Catalan's G | Easy | 2200 | Alternating series |
| ζ(2) → π | Medium | 23 + √ step | Square root extraction |
| Trapezoidal error | Medium | — | Integration API |
| Gauss circle O(r) | Medium | — | Geometric argument |
| Stirling / log(n!) | Hard | Same as γ | log bounds (like γ) |
| Barnes G | Very Hard | — | Requires Stirling + ζ'(-1) |
| 1/π (Chudnovsky) | Very Hard | 1 | Modular form identity |

## Recommended order

1. **e** — warmup, almost trivial
2. **ζ(-1) = -1/12** — one-liner from Mathlib
3. **ζ(3)** — already planned
4. **ln(2)** — same pattern as ζ(3), good practice
5. **Catalan's G** — same pattern, connects to L-functions
6. **π via ζ(2)** — builds on ζ(3) machinery + adds √ step
7. **Stirling** — hard but high-value

---

## Completed work: Cross-reference with OEIS and Wikipedia

All bounds proven in Lean 4.28.0 + Mathlib, using Euler-Maclaurin monotone
sequences evaluated at N = 23 via `norm_num`.

| s  | OEIS     | ζ(s) (20 digits)         | Proven lower        | Proven upper        | dp | File                |
|----|----------|--------------------------|---------------------|---------------------|----|---------------------|
|  3 | A002117  | 1.20205690315959428540   | 12020/10000         | 12021/10000         |  4 | Zeta3Bounds.lean    |
|  5 | A013663  | 1.03692775514336992633   | 103692/100000       | 103693/100000       |  5 | Zeta5Bounds.lean    |
|  7 | A013665  | 1.00834927738192282684   | 100834927/10^8      | 100834928/10^8      |  8 | Zeta7Bounds.lean    |
|  9 | A013667  | 1.00200839282608221442   | 10020083928/10^10   | 10020083929/10^10   | 10 | Zeta9Bounds.lean    |
| 11 | A013669  | 1.00049418860411946456   | 10004941886/10^10   | 10004941887/10^10   | 10 | Zeta11Bounds.lean   |
| 13 | A013671  | 1.00012271334757848915   | 10001227133/10^10   | 10001227134/10^10   | 10 | Zeta13Bounds.lean   |
| 15 | A013673  | 1.00003058823630702049   | 10000305882/10^10   | 10000305883/10^10   | 10 | Zeta15Bounds.lean   |
| 17 | A013675  | 1.00000763719763789976   | 10000076371/10^10   | 10000076372/10^10   | 10 | Zeta17Bounds.lean   |
| 19 | A013677  | 1.00000190821271655394   | 10000019082/10^10   | 10000019083/10^10   | 10 | Zeta19Bounds.lean   |
| 21 | A013679  | 1.00000047693298678781   | 10000004769/10^10   | 10000004770/10^10   | 10 | Zeta21Bounds.lean   |

Additional completed bounds:

| Constant        | OEIS    | Value (10 digits)  | File               |
|-----------------|---------|--------------------|--------------------|  
| π²              | A002388 | 9.8696044010...    | PiSqBounds.lean    |
| Catalan's G     | A006752 | 0.9159655941...    | CatalanBounds.lean |

Note: Higher s gives more decimal places at the same N because ζ(s) → 1
faster, making the Euler-Maclaurin tail smaller. The pattern A0136(63+2k)
for k=0,1,2,... covers ζ(5), ζ(7), ζ(9), ...

Files for s ≥ 9 are generated by `v28/playground/gen_zeta_bounds.py`.
