# Plan: proving `chudnovskySum = π⁻¹` following Milla (arXiv:1809.00533v6)

Target (in `pi.lean`, mirroring Mathlib's `proof_wanted chudnovskySum_eq_pi_inv`):

```
chudnovskySum = π⁻¹
-- where chudnovskySum = 12 / 640320^(3/2 : ℝ) * ∑' n, chudnovskyTerm n
--       chudnovskyTerm n = (-1)^n (6n)! (545140134 n + 13591409) / ((3n)! n!³ 640320^(3n))
```

Milla's paper (the tex files in `arXiv-1809.00533v6/`) is the reference proof. Its logical
structure splits into two halves:

1. **Analytic half** (ch. 1–8 → Main Theorem, `hauptformel`): for all τ with Im τ > 1.25,
   ```
   1/(2π·Im τ) · √(J(τ)/(J(τ)−1))
     = ∑ n, ((1−s₂(τ))/6 + n) · (6n)!/((3n)!(n!)³) · (1728·J(τ))⁻ⁿ
   ```
   with J = E₄³/(E₄³−E₆²) and s₂ = (E₄/E₆)·(E₂ − 3/(π·Im τ)). Fully self-contained in the paper.

2. **Arithmetic half** (ch. 9 + appendices A, B): at τ₁₆₃ = (1+i√163)/2,
   ```
   1728·J(τ₁₆₃) = −640320³        and        (1−s₂(τ₁₆₃))/6 = 13591409/545140134
   ```
   proved by "approximation + error bound + integrality ⇒ exact value". The integrality
   inputs are partly **cited from the literature** (see Phase C — the main open risk).

Substituting 2 into 1 and simplifying (`theohud`) gives the Chudnovsky formula; a final glue
step converts Milla's statement `√(640320³)/(12π) = ∑ …` into Mathlib's `chudnovskySum = π⁻¹`.

---

## What Mathlib (this repo's copy, v31) already provides

Strong and directly reusable:

| Paper item | Mathlib |
|---|---|
| ℘, ℘′, lattice, G_n, g₂, g₃, **℘′² = 4℘³ − g₂℘ − g₃** (`dglP`) | `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (`PeriodPair`, `weierstrassP`, `derivWeierstrassP_sq`, `G`, `g₂`, `g₃`, evenness, periodicity, meromorphy, power-series expansions) |
| E₄, E₆ as level-1 modular forms + q-expansions with σₖ(n) coefficients (`fouriertheorem`, part) | `NumberTheory/ModularForms/EisensteinSeries/*` (`E₄`, `E₆`, `E_qExpansion_coeff`) |
| E₂/G₂ quasi-modularity (≈ Legendre relation, see Phase A2) | `EisensteinSeries/E2/*` (`G2_S_transform`, `E2_slash_action`) |
| Δ = η²⁴, Δ = (E₄³−E₆²)/1728, Δ ≠ 0, q-product | `ModularForms/Discriminant.lean`, `Delta.lean`, `LevelOne/GradedRing.lean` |
| Dedekind η, log-derivative `logDeriv η = (πi/12)E₂` | `ModularForms/DedekindEta.lean` |
| ₂F₁ as a power series, radius 1 (`defihyp`, `satzkonv`) | `Analysis/SpecialFunctions/OrdinaryHypergeometric.lean` |
| Pochhammer symbols (`defpoch`) | `RingTheory/Polynomial/Pochhammer.lean` |
| Lambert series ∑ nᵏqⁿ/(1−qⁿ) = ∑ σₖ(n)qⁿ (`sigmaeisen`) | `NumberTheory/TsumDivisorsAntidiagonal.lean` |
| ODE uniqueness / Picard–Lindelöf (`satzclausen`, `omegastrich`) | `Analysis/ODE/*` (`ODE_solution_unique*`) |
| π bounds to arbitrary precision (`archim-lem`, `bemceulen`) | `Analysis/Real/Pi/Bounds.lean` (incl. bound-generating machinery) |
| Cauchy integral theory (rectangles, circles), removable singularities | `Analysis/Complex/CauchyIntegral.lean` etc. |
| IsIntegral / algebraic-integer machinery, rational algebraic integer ⇒ ℤ | `RingTheory/IntegralClosure/*` |

Missing (must be built):

- Weierstrass **ζ and σ** functions, quasiperiods η₁, η₂, σ transformation law, σ product formula.
- **j-invariant / Klein's J** (nothing in Mathlib), and everything about its CM values.
- **₃F₂**, hypergeometric ODEs, **Clausen's formula**.
- Picard–Fuchs equation, period integrals, Kummer's solution.
- Residue theorem as such (only assembleable from circle/rectangle Cauchy lemmas).
- Complex multiplication / singular moduli / class number 1 for ℚ(√−163).
- Verified interval numerics for e^{−π√N} to ~30 significant digits.

---

## File layout (mirrors the paper's chapters)

```
Playground/Pi/
  pi.lean               -- final: chudnovsky_formula_for_pi_inv (kept as is)
  Basic.lean            -- shared defs: L_τ as PeriodPair, q, J, s₂, E₂*, notation
  SigmaZeta.lean        -- [ch.1, 060] Weierstrass σ, ζ; convergence; σ odd; ζ' = −℘
  Liouville.lean        -- [ch.1, 060] Liouville thms 1–3 for elliptic functions
  WeierstrassMore.lean  -- [ch.1, 060] zeros of ℘′ (zerowp), e₁e₂e₃ factorization (pstrichprod)
  Quasiperiods.lean     -- [ch.2, 070] η(ω;L), η₁,η₂; Legendre relation; ω_k,η_k as integrals
  Lattices.lean         -- [ch.3, 080] scaling laws g_k(aL)=a^{-2k}g_k(L), η_k(aL)=η_k/a; J; L_J; satz44
  Fourier.lean          -- [ch.4, 090] σ product formula; η₁=π²E₂/3; g₂=(4/3)π⁴E₄; g₃=(8/27)π⁶E₆;
                        --            J = E₄³/(E₄³−E₆²); bridge PeriodPair.G ↔ eisensteinSeries
  Estimates.lean        -- [ch.5, 100] σₖ tail bounds; |1728J−1728J̃|<0.2; |s₂−s̃₂|<222000|q|³; E₆≠0
  Clausen.lean          -- [ch.6, 110] ₃F₂; ODEs for ₂F₁/₃F₂; Clausen's formula (satzclausen)
  PicardFuchs.lean      -- [ch.7, 120] d²Ω/dJ² + (1/J)dΩ/dJ + (31J−4)/(144J²(J−1)²)·Ω = 0
  Kummer.lean           -- [ch.8, 130] b(J) solves PF; omegastrich: Δ^{1/12}=2π·12^{-1/4}J^{-1/12}·₂F₁
  MainTheorem.lean      -- [ch.9, 140] thm35, thmglg10, thm42, darst, hauptformel
  DivisionValues.lean   -- [App.A, 160] F_m, division polynomials P_m, m·℘(u) algebraic integer
  ComplexMult.lean      -- [App.B, 170] κ; √D·(E₂*/η⁴)·(AC)² algebraic integer
  SingularModuli.lean   -- [cited inputs] j(τ) ∈ ℤ and s₂(τ) ∈ ℚ at class-number-1 CM points
  Numerics.lean         -- verified interval arithmetic: exp, π, rational q-polynomials
  Coefficients.lean     -- [ch.10, 150] 1728J(τ₁₆₃) = −640320³; s₂(τ₁₆₃) = 77265280/90856689; theohud
  Chudnovsky.lean       -- glue: theohud ⇒ chudnovskySum = π⁻¹ (rpow 3/2, ℚ-coercions, rearrangement)
  All.lean
```

Wire `Playground.Pi.All` into `Playground.lean` once files compile.

---

## Phase A — Analytic half up to the Main Theorem

### A0. `Basic.lean` — statements first (1–2 days)
Define, on top of Mathlib's `UpperHalfPlane` and `PeriodPair`:
- `Lτ : ℍ → PeriodPair` (ω₁ = 1, ω₂ = τ), `q τ = exp (2πiτ)`,
- `J τ := E₄ τ ^ 3 / (E₄ τ ^ 3 − E₆ τ ^ 2)` (define J directly via Eisenstein series, as the
  paper's `fouriertheorem` justifies; the lattice-theoretic g₂³/Δ form becomes a lemma),
- `E₂star τ := E2 τ − 3/(π · im τ)`, `s₂ τ := E₄ τ / E₆ τ * E₂star τ`.
Then state every theorem of ch. 1–9 as `sorry`-free-signature stubs. This pins the whole
dependency graph before any hard proof and lets work proceed in parallel.

### A1. σ, ζ, and the Liouville theorems (`SigmaZeta`, `Liouville`, `WeierstrassMore`)
- σ as `∏' l, (1 − z/l) · exp(z/l + z²/(2l²))` over `PeriodPair.lattice`; local uniform
  convergence (reuse the summability infrastructure from the Weierstrass file); σ odd;
  simple zeros exactly on L.
- ζ := logDeriv σ (Hadamard-style term-by-term); `deriv ζ = −℘` (matches Mathlib's
  `weierstrassP` term-by-term).
- Liouville 1 (elliptic + no poles ⇒ constant): easy — periodicity + compactness +
  `Differentiable.const_of_bounded`.
- Liouville 2 & 3 (residues sum to 0; #zeros = #poles): need a parallelogram contour.
  Mathlib has no residue theorem. Two options:
  (a) build a minimal "sum of residues over a fundamental parallelogram" lemma from
      `CauchyIntegral` primitives (real work, reusable);
  (b) **avoid where possible**: audit each use. `zerowp`/`pstrichprod` can be done by
      counting via `MeromorphicAt.order` and the argument principle already partially in
      Mathlib (`Analysis/Meromorphic/*`), or by direct elementary arguments (℘(z)−e_k has a
      double zero at ω_k/2 since ℘′ odd+periodic; injectivity of ℘ on a half-parallelogram).
  Decision point: prototype (b) first; fall back to (a) only if forced. Appendix A
  (`lemnullst`, `propfmprod`, `lemsigmasigma`) leans on Liouville 3, so some version is
  eventually needed — but "elliptic, poles only on L of known order, same zeros ⇒ ratio
  constant" (used everywhere) can be packaged once as a single workhorse lemma.

### A2. Quasiperiods and Legendre (`Quasiperiods`)
- `η k L := ζ(z + ω_k) − ζ(z)` well-defined (derivative is ℘(z) − ℘(z+ω_k) = 0).
- **Legendre relation** `η₁ω₂ − η₂ω₁ = 2πi`: the paper uses the residue theorem on a
  parallelogram. **Shortcut**: prove `η₁(Lτ) = G2 τ` (Eisenstein summation — Mathlib's `G2`
  uses exactly the `symmetricIcc` ordering) and derive Legendre from Mathlib's
  `G2_S_transform` (G₂(−1/τ) = τ²G₂(τ) − 2πiτ), which is equivalent. This also delivers
  `η₁ = π²E₂/3` (`fouriertheorem` part) almost for free via `E2`'s definition.
- Period/quasiperiod integral representations (`satzint`): formalize in z-space as
  `∫ t in 0..1, …` along β_k(t) (avoids defining contour integrals on the curve): trivial
  FTC + periodicity statements. Needed only by Picard–Fuchs.

### A3. Lattice scaling and J (`Lattices`) — routine
Reindexing sums: `G n (a • L) = a⁻ⁿ • G n L`, hence g₂, g₃, Δ, J scaling; ζ(az; aL) = ζ(z;L)/a
hence η_k scaling; `satz44` is algebra.

### A4. Fourier chapter (`Fourier`)
Much is already in Mathlib. Remaining real content:
- σ product formula (`fouriersigma`): the φ-function trick + "same quasi-periodicity, same
  zeros ⇒ ratio constant" (workhorse lemma from A1). Watch the sign issue Milla has in
  `satzphi` (the proof's `−e^{−2πiz}` is the correct transformation, not the displayed
  `−e^{2πiz}`).
- From it (or independently): `η₁ = π²E₂/3` (already via A2), and the lattice↔modular bridge
  `g₂(Lτ) = (4/3)π⁴·E₄ τ`, `g₃(Lτ) = (8/27)π⁶·E₆ τ`. Route: `PeriodPair.G 4/6` vs
  `eisensteinSeries` via `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries` + ζ(4)=π⁴/90,
  ζ(6)=π⁶/945 (both in Mathlib). This may make the full σ-product formula unnecessary for
  the main chain — it is needed again only in Appendix A (via `trafosigma`) — but
  `trafosigma` itself is elementary given A2.
- `J = E₄³/(E₄³−E₆²)` then follows from Mathlib's `discriminant_eq_E₄_cube_sub_E₆_sq`.

### A5. Estimates (`Estimates`) — mechanical but long
All of ch. 5: σₖ(n) ≤ n^{k+1}, geometric tail bounds, and the two headline theorems
(`theonaeherJ`: |1728J − 1728J̃| < 0.2 and |1728J| ∈ (0.737,1.321)/|q|; `theonaehers2`:
|s₂ − s̃₂| < 222000|q|³) for Im τ > 1.25, plus `lemE6` (|E₆| > 0.8). Pure `norm_num`/
`nlinarith`-style interval reasoning over explicitly truncated q-series; π bounds from
Mathlib replace Archimedes. Tedious, low-risk, fully parallelizable. Depends only on the
q-expansion identities (A4 / Mathlib).

### A6. Clausen chapter (`Clausen`) — self-contained, start immediately
- Define ₃F₂ (mirror `OrdinaryHypergeometric.lean`; consider upstreaming).
- Coefficient-shift dictionary (`koeffvergl`): term-by-term differentiation of power series
  (Mathlib: `FormalMultilinearSeries` / `hasFPowerSeriesOnBall.deriv` API).
- ODEs `dgl2f1`, `dgl3f2` via coefficient recurrences.
- **Clausen's formula**: both sides satisfy the same 3rd-order linear ODE + same first
  three Taylor coefficients. Two implementation options:
  (i) paper route: Picard–Lindelöf uniqueness for the linear system on (−1,1) — note z=0 is
      a *singular* point of the ODE, so uniqueness must be run on the power-series level or
      started at z₀ ≠ 0 after matching germs;
  (ii) **recommended**: pure formal-power-series proof — the ODE gives the same 3-term
      coefficient recurrence for (₂F₁)² (via Cauchy product) and ₃F₂; induction on n.
      Entirely algebraic, no analysis. Then upgrade to functions on |z|<1 by `tsum` equality.
- Finish with `darst`: (₂F₁(1/12,5/12;1;z))² = ∑ (6n)!/((3n)!(n!)³) (z/1728)ⁿ — the
  Pochhammer/factorial identity (6⁻³ⁿ·(1/6)ₙ(1/2)ₙ(5/6)ₙ = (6n)!/((3n)!12³ⁿ)): induction.

### A7. Picard–Fuchs and Kummer (`PicardFuchs`, `Kummer`) — the analytic crux
Paper route: differentiate the period integrals ω_k(g), η_k(g) under the integral sign,
exactness relations ∮ (xⁿ/y)′ dx = 0, solve a 3×3 linear system, change variables g ↔ J.
In z-space (A2 formulation) the exactness relations are FTC + periodicity; differentiation
under ∫₀¹ needs holomorphic-parameter dominated convergence (Mathlib:
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The subtlety: the integrand ℘(β(t); L_J)
depends on J through the lattice; fix instead the *algebraic* picture: parametrize
x = ℘(β_k(t)), y = ℘′(β_k(t)) at a base point and treat ∮ dx/y, ∮ x dx/y as functions of g
along a *fixed* contour in x-space — requires local constancy of contours (homotopy
invariance) OR keep everything in z-space with the τ-parametrized family and compute
∂/∂τ instead. **Decision point — recommended alternative**: replace ch. 7+8 by the
equivalent q-space computation: prove `omegastrich` in the form
```
E₄(τ) = (₂F₁(1/12, 5/12; 1; 1/J(τ)))⁴   for Im τ > 1.25   (equivalently Δ^{1/12} form)
```
via Ramanujan's derivative identities (D E₂ = (E₂²−E₄)/12 etc. — statable now with
Mathlib's `serreDerivative`; proofs exist to port from the sphere-packing-lean project
referenced in `ModularForms/Derivative.lean`), turning the PF equation into an ODE in q
with a formal-power-series uniqueness argument (regular point at q=0 after clearing the
J^{-1/12} factor; coefficient recurrence determines the solution uniquely given value at
q=0, computed from `theonaeherJ`-type limits). This keeps the *statement* of `omegastrich`
(the paper's ch. 8 output, which is all ch. 9 uses) while avoiding multivalued J-inversion
and contour homotopy. Keep the paper's contour proof as fallback/secondary.

### A8. Main Theorem (`MainTheorem`)
Given `omegastrich`, `theonaeherJ/s2`, `satzclausen`+`darst`, Legendre, and the scaling laws,
ch. 9 is a page of calculus: `thm35` (chain rule), `thmglg10` (algebra in E₂,E₄,E₆),
`thm42` (combine), then `hauptformel` = termwise differentiation of the series (A6 API) +
the **root-of-unity resolution**: at τ₈ = i√2 everything is real and positive
(`theonaeherJ/s2` numeric bounds), and both sides are continuous and nonvanishing on the
connected region Im τ > 1.25, so the principal branch is correct everywhere. Formalize the
branch argument only at the single point needed (τ₁₆₃ is what ch. 10 uses — but note
J(τ₁₆₃) < 0, so the continuity/connectedness argument from τ₈ **is** needed; plan it as a
lemma: two continuous functions on a connected set, equal up to unimodular factor,
agreeing at one point, both nonvanishing ⇒ equal).
Note Im τ₁₆₃ = √163/2 ≈ 6.38 > 1.25. ✓

## Phase B — Appendices A & B (integrality machinery, in-paper)

### B1. `DivisionValues` [App. A]
Division points DIV(m), F_m = σ(mz)/σ(z)^{m²}, the σ three-term identity, F_m recursions,
division polynomials P_m ∈ ℤ[x,h₂,h₃] with the four-case recursion, `thmbaker`
(m²∏(x−℘(u)) = P_m² · (4(x³−h₂x−h₃))^{[m even]}), structure lemmas, and the two outputs:
- `theowpsum`: ∑_{u ∈ DIV(m)} ℘(u) = 0 (needed by B2),
- `theomwpu`: l_m·℘(u) integral over ℤ[¼g₂, ¼g₃] (l_m = m or m/2).
Self-contained given A1/A2 (σ, ζ, Liouville workhorse, `laurentwp`-grade expansions,
duplication formula). Heavy but elementary; the P_m induction is a good candidate for
`decide`-free careful `ring` work. Largest single file by volume.

### B2. `ComplexMult` [App. B]
κ := (Aη₁ − Cτη₂)/ω₂; `lemkapa1` (κ = −√D·π²E₂*/(3ω₁²), uses Legendre + η₁ = π²E₂/3);
elliptic ζ-combination, residue bookkeeping (Liouville workhorse), `lemkapa2`
(Cτκ = −∑_{v ∈ DIV(Cτ)} ℘(v), uses B1's `theowpsum`); conclude with lattice rescaling
L̂ = (π/√3)η(τ)²·L_τ:
```
√D·(E₂*(τ)/η(τ)⁴)·(AC)² is an algebraic integer    (theoezweisternrest)
```
where 1728η²⁴ := E₄³ − E₆² (Mathlib's Δ; no η-transformation theory needed).
Also `satzezweistern`'s easy parts: E₄/η⁸, E₆/η¹² integral (roots of X³−j, X²−(j−1728)).

## Phase C — the cited inputs (`SingularModuli`) — MAIN RISK

The paper does **not** prove these; they must be formalized from scratch or found:

1. **j(τ) is an algebraic integer for CM τ** [Silverman ATAEC II.6.1]. Only needed at
   τ₁₆₃ (and τ₈ if ch.-9-style exactness is wanted there — it is not; τ₈ is used only for
   the branch argument, which needs no integrality). Candidate route (classical, self-
   contained): modular polynomial Φ_m — build the function field theory of level-1 modular
   forms far enough to get Φ_m ∈ ℤ[X,Y] (q-expansion principle + elementary symmetric
   functions over the m-isogeny orbit) and Kronecker's lemma (Φ_m(X,X) has unit leading
   coefficient for non-square m); then Cτ·L_{τ₁₆₃} ⊆ L_{τ₁₆₃} with norm m = AC = 41 gives
   Φ₄₁(j(τ₁₆₃), j(τ₁₆₃)) = 0. This is a serious project on its own (comparable to what
   exists for Δ/E₄/E₆ today).
2. **degree j(τ) = h, i.e. here j(τ₁₆₃) ∈ ℚ** [Silverman II.4.3(b) + h(−163) = 1 via
   Buell]. h(−163) = 1 itself is a finite reduced-forms computation (`decide`-able once
   binary quadratic form reduction is set up; Mathlib has none of it, but it is small).
   The hard part is "conjugates of j(τ) are the j(τ_Q)" — the main theorem of complex
   multiplication. No shortcut known within Milla's framework.
3. **s₂(τ) ∈ ℚ(j(τ))** [Masser 1975 Thm A1]. Masser's own appendix proof is elliptic-
   function-theoretic (same toolbox as App. B) but nontrivial; needs its own outline pass.

Honest assessment: Phase C is where most of the total effort lies (likely > half). It is
also completely decoupled from Phases A/B/D: everything else can be finished with C's
three statements as explicit hypotheses. **Recommended intermediate deliverable**:
```
theorem chudnovsky_of_singular_moduli
    (h₁ : (1728 : ℂ) * J τ₁₆₃ = -640320^3 →→ replaced by: IsIntegral ℤ (1728 * J τ₁₆₃))
    (h₂ : ∃ r : ℚ, s₂ τ₁₆₃ = r) … : chudnovskySum = π⁻¹
```
i.e. the full paper minus the three citations — already a publishable formalization that
turns Mathlib's `proof_wanted` into a precisely-scoped CM problem. (Note: h₁ as stated
needs "∈ ℤ", i.e. items 1+2 together.)

## Phase D — numerics and assembly

### D1. `Numerics` — verified evaluation
Need, with proven error bounds:
- π to ~30 significant digits (extend `Analysis/Real/Pi/Bounds.lean` machinery — it is
  built to generate arbitrary-precision bounds; may need a longer certified iteration).
- `exp(−π√163)` etc. to ~30 digits: rational interval arithmetic + `Real.exp_bound`
  Taylor remainder; √163 by rational approximation + `nlinarith`. Package as a tiny
  interval-arithmetic layer over ℚ (add/mul/div/exp/sqrt with directed rounding), or
  adopt an existing Lean interval tactic if one is available by then.
- Evaluate the two truncations: 1728·J̃ = (1+240(q+9q²))³/(q(1−q−q²)²⁴) and
  s̃₂·b₁₆₃ — plain ℚ arithmetic on the certified q-interval (q = −e^{−π√163}).

### D2. `Coefficients` [ch. 10]
- `jwert2` at N = 163 only: |1728J − 1728J̃| < 0.2 (A5) + 1728J̃ within 0.2−ε of −640320³
  (D1) + 1728·J(τ₁₆₃) ∈ ℤ (Phase C) + "unique integer within <1/2" ⇒ exact.
- `s2nenner` + `satzhilfszahlen` at N = 163: b₁₆₃ = 10996566783048 exactly (integer
  arithmetic: c=1, b² = D(j−1728)(AC)⁴ — perfect-square check with j = −640320³, D = −163,
  A = 41, C = 1 — `decide`/`norm_num`); a₁₆₃ := s₂·b integral (B2 + √c trivial for c = 1;
  the product identity `produ` needs E₆(τ₁₆₃) ≠ 0 from A5) and rational (Phase C) hence
  ∈ ℤ; |ã − a| ≤ 222000|q|³·b < 0.01 (A5 + D1) ⇒ a₁₆₃ = 9351571368960 exactly;
  s₂(τ₁₆₃) = 77265280/90856689, (1−s₂)/6 = 13591409/545140134 (`norm_num`).

### D3. `Chudnovsky` — glue to `chudnovskySum = π⁻¹`
- Substitute τ₁₆₃ into `hauptformel`; Im τ₁₆₃ = √163/2; simplify
  √(J/(J−1)) with 1728J = −640320³: J/(J−1) = 640320³/(640320³+1728) and
  640320³ + 1728 = 1728·163·(3·7·11·19·127·… )² — concretely verify
  640320³+1728 = 163·(12·53360)²·… by `norm_num`; track the principal branch (LHS real
  positive — needs the A8 branch lemma since J < 0 here).
- Convert to Mathlib's form: `640320^(3/2 : ℝ) = 640320 * √640320` (rpow lemmas),
  `chudnovskyTerm` ℚ→ℝ coercion, merge the two series
  ∑ ((1−s₂)/6 + n)·… = (1/545140134)·∑ (13591409 + 545140134n)·… (linearity of tsum,
  absolute convergence from ratio test — needed anyway for `hauptformel`), and invert
  (both sides positive). Finish `chudnovsky_formula_for_pi_inv`.

---

## Suggested execution order (maximizing early wins & parallelism)

1. **A0** stubs — pins all statements.  [small]
2. **A6 Clausen** (independent of everything) + **A5 Estimates** (needs only q-expansion
   defs) + **D1 Numerics** (independent) — three parallel tracks.  [each medium]
3. **A1–A4** σ/ζ/Liouville-workhorse/quasiperiods/Fourier bridge.  [large]
4. **A7 Kummer** (decide contour vs. Ramanujan-identities route early — prototype both
   on paper first) then **A8 Main Theorem**.  [large, highest analytic risk]
5. **B1, B2** appendices (parallel with 4).  [large but elementary]
6. **Milestone: `chudnovsky_of_singular_moduli`** (everything modulo Phase C).
7. **Phase C** singular moduli — its own multi-stage plan (modular polynomials →
   integrality; reduced forms → h(−163)=1; Masser A1 → s₂ rationality); revisit
   literature/other formalization efforts (sphere-packing-lean Ramanujan identities;
   any modular-polynomial work) before starting.
8. **D2–D3** assembly; wire `Pi/All.lean` into `Playground.lean`.

## Known traps (collected from the analysis)

- `satzphi` sign typo in the paper: transformation is φ(z+τ) = −e^{−2πiz}φ(z) (the proof's
  version), not the displayed −e^{+2πiz}.
- `defltilde` typo: ℤω̃₁ + ℤω̃₂ (paper prints ω̃₁ twice).
- All intermediate root-taking is "up to a root of unity"; only A8's connectedness
  argument makes anything exact. Don't chase branch bookkeeping inside ch. 6–8; state
  intermediate identities in squared/branch-free forms wherever possible.
- Mathlib's ₂F₁ is defined for a general Banach algebra via `FormalMultilinearSeries`;
  check early that the deriv/coefficient API is comfortable for the ODE work, else work
  with raw `PowerSeries ℚ` in A6 and coerce at the end.
- `chudnovskyTerm` is ℚ and the sum sign-alternates: use `Summable` of the absolute
  series ((6n)!/((3n)!(n!)³) ≤ 12³ⁿ·(binomial bounds) and 640320³ ≫ 12³) — needed in
  three places (hauptformel, D3, and A6's radius work).
- The estimates chapter constants (222000, 0.2, 0.737…) are all for Im τ > 1.25; τ₈ = i√2
  (Im = 1.414) and τ₁₆₃ (Im ≈ 6.38) both qualify, but don't weaken 1.25 anywhere.

## Effort estimate (rough, in units of "focused person-weeks")

| Phase | Estimate |
|---|---|
| A0 stubs | 1 |
| A1–A4 σ/ζ/Fourier | 6–10 |
| A5 estimates | 3–5 |
| A6 Clausen | 3–5 |
| A7–A8 Kummer + Main Thm | 8–12 |
| B1–B2 appendices | 8–12 |
| C singular moduli | 25–60 (dominant, high variance) |
| D numerics + assembly | 4–6 |

Total ≈ 60–110 person-weeks. The `chudnovsky_of_singular_moduli` milestone (everything
except C) ≈ 35–50.
