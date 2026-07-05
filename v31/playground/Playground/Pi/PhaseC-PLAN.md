# Phase C plan: the singular-moduli inputs (`SingularModuli.lean`)

Scope: the four `sorry`s in `Playground/Pi/SingularModuli.lean`, the last mathematical
content of the whole project apart from the in-progress Appendix A/B work:

1. `isIntegral_j_τ₁₆₃` : `IsIntegral ℤ (1728 * J τ₁₆₃)`;
2. `j_τ₁₆₃_rational`  : `∃ r : ℚ, 1728 * J τ₁₆₃ = r`;
3. `s₂_τ₁₆₃_rational` : `∃ r : ℚ, s₂ τ₁₆₃ = r`;
4. `j_τ₁₆₃_integer`   : `∃ m : ℤ, 1728 * J τ₁₆₃ = m` (= 1 + 2 via
   `isInt_of_integral_of_rat`, already proved — private in `Coefficients.lean`).

What downstream actually consumes (checked against `Coefficients.lean`): only
`j_τ₁₆₃_integer` (in `jwert_τ₁₆₃`) and `s₂_τ₁₆₃_rational` (in `s₂_τ₁₆₃`, together with
the App.-B integrality `theoezweisternrest_of_isIntegral_j`, whose `IsIntegral ℤ (1728·J)`
hypothesis is discharged from `jwert_τ₁₆₃`). Statements 1–2 are stepping stones. **No
change to the four pinned statements is needed**; the routes below produce exactly them.
(Housekeeping: un-private `isInt_of_integral_of_rat` and prove statement 4 from 1+2 in
`SingularModuli.lean` itself, so `Coefficients.lean` keeps a single entry point.)

Everything below is scoped to `τ₁₆₃` and class number 1. None of the general theory
(main theorem of CM, class fields, Shimura reciprocity) is needed; the plan exploits
h(−163) = 1 aggressively.

**Headline recommendation.** One shared piece of infrastructure — the modular polynomial
`Φ_m ∈ ℚ[X,Y]` for prime `m`, built by elementary q-expansion bookkeeping — powers all
three statements:

- statement 1 via the ℤ-refinement `Φ₄₁ ∈ ℤ[X,Y]` + Kronecker's unit-leading-coefficient
  lemma (classical route, no shortcut exists);
- statement 2 via a **three-prime conjugation argument** (`m ∈ {41, 43, 61}`) plus the
  valence theory of `j` and a finite reduced-forms computation — this replaces the main
  theorem of CM entirely at h = 1;
- statement 3 via **Masser's own Appendix-1 proof** (recovered in full from LNM 437, see
  §5), which needs only `Φ₁₆₃ ∈ ℚ[X,Y]`, a matrix classification lemma, and the Ramanujan
  derivative identities — **already fully proved in this project's `Ramanujan.lean`**.

Estimated total: **20–35 focused person-weeks**, below the old PLAN.md guess of 25–60,
because (a) Masser's actual proof turned out to be modular-polynomial calculus, not new
elliptic-function theory; (b) the rationality shortcut avoids CM/CFT; (c) Ramanujan
identities and the App.-B integrality already exist in-project.

---

## 1. Survey of existing formalizations (as of July 2026)

Verified against this repo's Mathlib copy (`fabf563a`, 2026-06-15) and by web survey of
upstream Mathlib, Isabelle/AFP, Coq/Rocq, and project repos.

**In Mathlib now (directly reusable):**

| Item | Where |
|---|---|
| q-expansion API: `cuspFunction`, `qExpansion` (as `PowerSeries`), `hasSum_qExpansion`, `qExpansion_mul/add/smul`, coefficient-by-integral, uniqueness | `NumberTheory/ModularForms/QExpansion.lean` |
| `E₄`, `E₆` q-expansions with `σₖ(n)` coefficients (`E_qExpansion_coeff`) | `EisensteinSeries/QExpansion.lean` |
| `E2` + transformation law; η, Δ = η²⁴ with q-product, `Δ ≠ 0`, `Δ = (E₄³−E₆²)/1728` | `E2/*`, `DedekindEta.lean`, `Discriminant.lean`, `LevelOne/GradedRing.lean` |
| Level-1 structure: weight-0 forms constant (`levelOne_weight_zero_const`), negative weight zero, dimension formulas, Sturm bound | `LevelOne/*` |
| `slash_action_generators_SL2Z` (S,T generate — check invariance on generators) | `LevelOne/Basic.lean` |
| SL(2,ℤ) fundamental domain `𝒟`, `exists_smul_mem_fdo` | `NumberTheory/Modular.lean` |
| `IsIntegral` / `IsIntegrallyClosed` (rational algebraic integer ⇒ ℤ — already used as `isInt_of_integral_of_rat` in `Coefficients.lean`); ring-closure of algebraic integers | `RingTheory/IntegralClosure/*` |
| Newton's identities (power sums ↔ elementary symmetric) | `Mathlib/Combinatorics/Enumerative` / `RingTheory` (`MvPolynomial` Newton identities) |
| `minpoly` API, `IsAlgClosed.lift` (extend embeddings to ℂ), `Polynomial.eq_prod_roots_of_splits` | `FieldTheory/*` |
| Number-field class numbers via Minkowski: `classNumber`, `classNumber_eq_one_iff`, `isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime` | `NumberTheory/NumberField/ClassNumber.lean` |
| Open mapping theorem, identity theorem, meromorphic order/Laurent machinery | `Analysis/Complex/*`, `Analysis/Meromorphic/*` |

**Not in Mathlib, not anywhere else — must be built from scratch:**

- The analytic j-invariant. `Mathlib/NumberTheory/ModularForms/JInvariant.lean` does
  **not** exist (in this copy or upstream); no `jInvariant` declarations anywhere. (The
  *algebraic* `WeierstrassCurve.j` exists but there is no analytic↔algebraic bridge; we
  don't need it.) This project's `J` (in `Basic.lean`) already is the definition; Phase C
  adds its q-expansion and valence theory.
- **Modular polynomials Φ_m / Kronecker congruence: no formalization in any assistant.**
- **Singular moduli / CM / class polynomials: no formalization in any assistant.**
  (Buzzard's ClassFieldTheory project is active but global CFT is far off — irrelevant
  for us since the h = 1 shortcut avoids it.)
- **Binary quadratic form reduction / form class groups: nothing in Mathlib** (only
  general quadratic-form algebra). Explicit *field* class-group computations exist
  (Baanen–Best–Coppola–Dahmen CPP 2023; Banwait's ℤ[(1+√−7)/2] work 2026) — usable
  patterns, but the *form*-reduction route below is more direct for our purpose.
  h(−163) = 1 itself: never formalized anywhere.
- Hecke operators: Mathlib PRs in flight (#40934, Birkbeck's #41251+ series, June–July
  2026). **Do not block on these**: our bespoke prime-`m` coset machinery is small, and
  the abstract Hecke-ring layer wouldn't give us the ℤ[ζ_m]-expansion bookkeeping anyway.
  Revisit if they land mid-project.

**Design references elsewhere:**

- Isabelle/AFP "Complex Lattices, Elliptic Functions, and the Modular Group" (Eberl–
  Bordg–Li–Paulson, 2024/25): has Klein's J, its Γ-invariance, the **valence formula**,
  and "**J is a bijection from the (closed-half) fundamental region to ℂ**" (used for
  Picard's little theorem). No Φ_m, no CM, no singular moduli. This is the best proof
  blueprint for our `Valence.lean`; not directly portable but the proof skeletons are.
- Sphere-Packing-Lean: Ramanujan derivative identities — already ported/reproved in this
  project (`Ramanujan.lean`: `deriv_E2`, `deriv_E₄`, `deriv_E₆`, `deriv_discriminant`,
  all sorry-free). Nothing further needed from there.
- Masser, *Elliptic Functions and Transcendence*, LNM 437 (1975), Appendix One: full text
  recovered; proof structure mapped in §5. Modern restatements that cross-check it:
  Bruinier–Ono–Sutherland arXiv:1301.5672 (their Lemma 2.3 *is* Masser's γ-formula),
  Mertens–Rolen arXiv:1501.03743 (eq. (2.6)), Zagier 1-2-3 §6.3 Prop. 27 (the weight-2
  `E₂* − E₂*|₂M` trick, algebraicity only).
- Guillera arXiv:2003.06668 gives a different (hypergeometric) proof of the Chudnovsky
  series; adopting it would abandon Milla's framework and all completed work — not an
  option, noted only for completeness.

---

## 2. Arithmetic facts at τ₁₆₃ (sanity-checked numerically; re-verify in Lean by `decide`)

CM data (already in `ComplexMult.lean`): `41 − τ + τ² = 0`, i.e. `(A,B,C) = (41,−1,1)`,
`D = −163`, `2Cτ + B = i√163`, `ττ̄ = 41`, `τ + τ̄ = 1`.

- Norm form of ℤ[τ] = O_{ℚ(√−163)}: `x² + xy + 41y²`. Its values: smallest non-square
  values are **41, 43, 47, 53, 61, 71, 83, 97, …** (Euler's `n² + n + 41`); every prime
  `< 41` is inert. So **m = 41 is the smallest usable modular-polynomial index**, no
  shortcut with tiny `m` exists. `(−163/p) = −1` for `p = 2,3,5,7,…,37`.
- Reduced forms of discriminant −163 (`|b| ≤ a ≤ c`, `b² − 4ac = −163`): only
  `(1, 1, 41)`. Hence h(−163) = 1. (Minkowski bound cross-check: `(2/π)√163 ≈ 8.13`;
  2, 3, 5, 7 all inert.)
- Fixed-point matrices at τ₁₆₃ (used in §§4–5): for `α = n + τ` (norm `n² + n + 41`),
  the matrix of α on the basis `(τ, 1)` fixes τ₁₆₃; explicitly `M_n = [[n+1, −41],[1, n]]`
  (check: `(a τ + b)/(c τ + d) = τ ⟺ τ² = τ − 41`), `det M_n = n² + n + 41`,
  `tr M_n = 2n + 1`, and `tr² − 4·det = −163` — always λ = 1. Instances:
  `n = 0 → det 41`, `n = 1 → det 43`, `n = 4 → det 61`. The trace-zero matrix
  `Λ = [[1, −82],[2, −1]]` (Masser's) has `det Λ = 163`, `Λτ = τ`, `Λ′(τ) = −1`.
- **Modular polynomial sizes** (why "compute Φ explicitly" is dead on arrival): Φ_m for
  prime m has degree m+1 in each variable; largest coefficient ≈ 10^397 for m = 41,
  10^421 for 43, 10^653 for 61. All routes below use only *existence and abstract
  properties* of Φ_m; no coefficient is ever computed.
- **Discriminant enumeration for the rationality argument** (§4): for an integral matrix
  `M`, `det M = m`, fixing some `τ′ ∈ ℍ`, the primitive integral quadratic of τ′ has
  discriminant `D₀ < 0` with `t² − 4m = λ²·D₀`, `t = tr M`, `λ ∈ ℤ≥1`. The possible D₀:
  - m = 41: {−164, −163, −160, −155, −148, −139, −128, −115, −100, −83, −64, −43, −40, −32, −20, −16, −8, −4}
  - m = 43: {−172, −171, −168, −163, −156, −147, −136, −123, −108, −91, −72, −51, −43, −39, −28, −27, −19, −12, −8, −7, −3}
  - m = 61: {−244, −243, −240, −235, −228, −219, −208, −195, −180, −163, −144, −123, −100, −75, −60, −52, −48, −36, −27, −20, −19, −16, −15, −12, −4, −3}. Crucially:
  - **41 ∩ 43 ∩ 47 = {−163, −43} — the "obvious" triple FAILS** (−43 = 11²−164 = 0²−172·(λ=2)… survives);
  - **41 ∩ 43 ∩ 61 = {−163}** ✓ (also 41 ∩ 47 ∩ 61 works). No pair suffices.
  This must be re-verified inside Lean as a `decide`/`interval_cases` lemma, not trusted
  from here.

---

## 3. Statement 1 — integrality of j(τ₁₆₃): route analysis

### 3.1 Recommended: classical modular-polynomial route (no alternative exists)

There is no known integrality proof avoiding either Φ_m or reduction-mod-p CM theory
(much heavier). Weber/eta class invariants (`f`-functions) would need level-48 modular
functions plus their own integrality theory — strictly worse. Kronecker's Φ_m route it is,
but organized to be as Lean-shaped as possible. All of §3 is for **prime `m`** (41 is all
statement 1 needs; the same files instantiate m = 43, 61, 163 for §§4–5).

Sub-lemma chain (names indicative):

**(B1) j has a q-expansion `1/q + ℤ⟦q⟦` — `JFunction.lean`.**
`j := 1728·J = E₄³/Δ` (`mul_J_eq`, proved). Two options for ℤ-coefficients of Δ:
  (a) via Mathlib's η q-product: `Δ = q·∏(1−qⁿ)²⁴`, so `Δ/q` is a power series with
      ℤ coefficients and constant term 1 (recommended — no congruence needed);
  (b) via `1728 ∣ E₄³ − E₆²` coefficientwise in `PowerSeries ℤ` (elementary but fiddly).
Then `Δ/q` is a unit in `ℤ⟦q⟧` (constant term 1), and `j·q = E₄³·(Δ/q)⁻¹` has ℤ
coefficients, constant term 1. Deliverable: a structure carrying "meromorphic-at-∞
invariant function + its principal part," or simply the pair of facts
`cuspFunction (j·q-side) analytic` + `qExpansion coefficients ∈ ℤ` + leading coefficient
1. Also here: `j (γ • τ) = j τ` for `γ ∈ SL(2,ℤ)` (from E₄, E₆ modularity; check on S, T
via `slash_action_generators_SL2Z`).

**(B2) the m-isogeny orbit — `CosetOrbit.lean`.**
For prime m, define the m+1 functions `f_∞(τ) = j(mτ)`, `f_i(τ) = j((τ+i)/m)`
(i = 0,…,m−1), i.e. index by `Option (ZMod m)` or `Fin (m+1)`. Prove:
- each `f_i` is holomorphic on ℍ (composition; the maps are ℍ-self-maps);
- **T-permutation**: `f_i(τ+1) = f_{i+1}(τ)` (i ∈ ZMod m, wrap via `j((τ+m)/m) = j(τ/m)`
  by T-invariance of j), `f_∞(τ+1) = f_∞(τ)`;
- **S-permutation**: `f_∞(−1/τ) = f_0(τ)`, `f_0(−1/τ) = f_∞(τ)`, and for `i ≠ 0`
  `f_i(−1/τ) = f_{i′}(τ)` with `i′ = −i⁻¹` in `(ZMod m)ˣ`, via the *explicit* matrix
  `γ = [[−i′, (1+ii′)/m],[−m, i]] ∈ SL(2,ℤ)` (integrality ⟺ `m ∣ 1 + ii′`; det = 1 by
  construction). No Hecke theory needed — two finite permutation lemmas.
Conclusion: the multiset `{f_i(τ)}` is SL(2,ℤ)-invariant (via S,T generation).

**(B3) power sums have ℚ q-expansions — `ModularPolynomialQ.lean`.**
`p_k(τ) := Σ_i f_i(τ)^k` = the weight-0 Hecke sum of `j^k`. The classical computation:
for `f` with Laurent expansion `Σ c_n qⁿ` (c_n ∈ ℤ, finite principal part),
`Σ_{b mod d} f((aτ+b)/d) = d · Σ_{d∣n} c_n q^{na/d}` — the root-of-unity averaging
`Σ_{b mod d} ζ_d^{bn} = d·[d∣n]` (Mathlib has geometric sums of roots of unity). Hence
`p_k ∈ ℚ((q))` — **no ζ_m survives, no Galois theory**. (Analytic form: reindexing of
absolutely convergent Laurent series.)

**(B4) elementary symmetric functions: `∏_i (X − f_i) = Σ_k S_k(τ) Xᵏ` with
`S_k ∈ ℚ((q))`** — Newton's identities (Mathlib) over a ℚ-algebra convert (B3) into
rationality of the `S_k` q-expansions. Char 0 only — this is where ℤ is *not* yet
available (Newton divides by k!).

**(B5) the q-expansion principle: invariant + holomorphic + `R((q))`-expansion ⇒
`R[j]`,** for `R ∈ {ℚ, ℤ}` a subring of ℂ. Downward induction on the pole order N of the
cuspFunction at 0 (Mathlib's `MeromorphicAt`/order machinery on the disk side): subtract
`a_{−N}·j^N` (j-expansion is monic `1/q + ℤ⟦q⟧`, so this reduces pole order and keeps
R-coefficients), end at "holomorphic + invariant + bounded ⇒ constant" — package the
remainder as `ModularForm 𝒮ℒ 0` and use Mathlib's `levelOne_weight_zero_const`.
Output: `S_k = 𝒮_k(j)` for polynomials `𝒮_k ∈ ℚ[X]`, i.e.
**`Φ_m(X, Y) := Σ_k 𝒮_k(Y)·Xᵏ ∈ ℚ[X][Y]` with `∀ τ, Φ_m(X, j τ) = ∏_i (X − f_i τ)`.**
This identity-for-all-τ is the keystone consumed by §§4–5.

**(B6) ℤ-refinement — `ModularPolynomialZ.lean`** (needed only for m = 41):
each q-coefficient of `S_k` is (i) rational by (B4), (ii) an **algebraic integer**,
because the `f_i` have expansions in `ℤ[ζ_m]((q^{1/m}))` (substitute `q ↦ ζ_m^i q_m^a`
into j's ℤ-expansion; coefficients stay in the subring ℤ[ζ_m], whose elements are
integral — ring closure of `IsIntegral`, in Mathlib) and T-invariance kills the
non-integral powers of `q_m`. Then `IsIntegrallyClosed.isIntegral_iff` gives
coefficients ∈ ℤ, and (B5) with R = ℤ gives `𝒮_k ∈ ℤ[X]`, `Φ₄₁ ∈ ℤ[X,Y]`.
*Implementation note:* represent the `q_m = q^{1/m}` expansions concretely as
(finite principal part in `q_m⁻¹`) + `PowerSeries ℤ[ζ_m]`, evaluated analytically at
`q_m(τ) = exp(2πiτ/m)`; avoid `HahnSeries`/`LaurentSeries` friction. The Galois action
is **never** needed — this is the main simplification over the textbook proofs
(Lang, Silverman): rationality comes from (B3)–(B4), integrality from ring closure,
and they are combined pointwise per coefficient.

**(B7) Kronecker's lemma** (m nonsquare, here m = 41): `G_m(X) := Φ_m(X, X) ∈ ℤ[X]` has
leading coefficient ±1. Proof by leading q-coefficient of `∏_i (j − f_i)`:
`j − f_∞ = −q^{−m}(1 + O(q_m))` and `j − f_i = ζ_m^{−i} q_m^{−1}(1 + O(q_m))`
(no cancellation of leading terms precisely because `m` is not a square, so `a ≠ d` in
every coset; for prime m: 1 ≠ m). The total leading coefficient is
`± ζ_m^{−Σi} = ±ζ_m^{−m(m−1)/2} = ±1` (m odd). Since it is also *the* integer leading
coefficient of `G_m`, it is ±1. Also record `deg G_m` and `G_m ≠ 0`.

**(B8) the CM relation `Φ₄₁(j τ₁₆₃, j τ₁₆₃) = 0` — `CMRelations.lean`.**
Show `f_0(τ₁₆₃) = j(τ₁₆₃)`, purely in ℍ (no lattices): with `γ = [[0,1],[−1,1]]`,
`γ·(τ/41) = 41/(41−τ) = (τ−1)/τ = TS·τ` — a two-line Möbius computation from
`τ² = τ − 41` — hence `j(τ₁₆₃/41) = j(TS τ₁₆₃) = j(τ₁₆₃)`. So one factor of
`Φ₄₁(X, j τ₁₆₃)` at `X = j τ₁₆₃` vanishes.

**(B9) conclusion**: `G₄₁` monic-up-to-sign in ℤ[X], `G₄₁(1728·J τ₁₆₃) = 0` ⇒
`isIntegral_j_τ₁₆₃`. (Negate G if the sign is −1: `IsIntegral` from a ±monic annihilator.)

### 3.2 Rejected alternatives (assessed)

- **Smaller m**: impossible; 41 is the smallest non-square norm (see §2). Composite or
  square m don't help (squares break Kronecker; composites aren't norms below 41).
- **Explicit Φ_m coefficients** (for this or any statement): coefficients up to 10^400,
  and certifying them would need q-expansion arithmetic to ~900 terms with such integers.
  Dead. All uses are abstract.
- **Weber/eta-quotient class invariants**: replaces Φ₄₁ with smaller polynomials but
  requires level-48 modular function theory + its own rationality/integrality machinery.
  Strictly more infrastructure. Rejected.

---

## 4. Statement 2 — rationality of j(τ₁₆₃): route analysis

### 4.1 What the literature proof needs, and what we actually need

The textbook statement "deg j(τ) = h(−163) = 1" (Silverman ATAEC II.4.3(b)) rests on the
main theorem of CM: *every Galois conjugate of j(τ_K) is j(a) for an ideal class a*. Its
standard proofs (Silverman via Deuring reduction; Cox §11 via the analytic class-field
apparatus; Shimura) all need the algebraic-geometry ↔ lattice dictionary: uniformization
of complex elliptic curves, transport of the endomorphism ring under `Gal(ℚ̄/ℚ)` acting on
curve coefficients, and `End`-rings as rational maps. In Lean today that dictionary is the
single most expensive missing bridge (Mathlib has `WeierstrassCurve` + group law, but no
analytic uniformization, no endomorphism rings, no isogenies-as-lattice-inclusions).
A poor-man's numerical approach (certify j as the unique suitable root of `Φ₄₁(X,X)`)
fails: it cannot control *conjugates* (they may be other, unknown, roots) and the
coefficients are astronomical anyway.

**But at h(−163) = 1, with Φ_m available for several m, there is a conjugation-free
argument** that avoids curves, uniformization of curves, End-rings, CFT — everything —
at the price of the *valence theory of j* (injectivity mod Γ and surjectivity), both of
which are self-contained complex analysis with strong prior art (Isabelle did both).

### 4.2 Recommended: the three-prime argument

Fix `j₀ := 1728·J τ₁₆₃`, algebraic by statement 1. Let `x ∈ ℂ` be any root of
`minpoly ℚ j₀`. Chain:

**(C1)** There is a field embedding `σ : ℚ(j₀) → ℂ` with `σ j₀ = x` (Mathlib:
`minpoly` roots ↔ `AlgHom`s via `AdjoinRoot.lift` / `IntermediateField` API).

**(C2)** For each `m ∈ {41, 43, 61}`: `Φ_m(j₀, j₀) = 0` (§3's (B8) for m = 41; same
explicit Möbius computations for `α = 1 + τ` (norm 43) and `α = 4 + τ` (norm 61) in
`CMRelations.lean`). Since `Φ_m ∈ ℚ[X,Y]`, applying σ gives **`Φ_m(x, x) = 0`**.

**(C3) Valence input.** `j : ℍ → ℂ` is surjective, and `j τ = j τ′ ⇒ τ′ ∈ Γ·τ`.
(Sub-plan in §4.3.) Pick `τ′` with `j τ′ = x`.

**(C4)** From `Φ_m(x, x) = ∏_i (x − f_i(τ′)) = 0`: some `f_i(τ′) = j(τ′)`, so by (C3)
`A_i τ′ = γ τ′` for the coset matrix `A_i` (det m) and some `γ ∈ SL(2,ℤ)`; then
`M := γ⁻¹A_i` is an **integral matrix of determinant m fixing τ′** (primitive is
automatic: `g ∣` all entries ⇒ `g² ∣ m` prime ⇒ `g = 1`; and `c ≠ 0`, else `M` scalar
and `m` a square).

**(C5)** The three matrices (dets 41, 43, 61) fix a priori three *different* points
`τ′_m`, all Γ-equivalent (same j-value x + injectivity). Conjugating by the connecting
γ's (SL(2,ℤ)-conjugation preserves integrality, det, trace), get **three integral
matrices fixing one common τ′₀**. Each gives an integral quadratic
`c z² + (d−a) z − b` vanishing at τ′₀; each is an integer multiple (Gauss content
argument) of the *primitive* integral quadratic `(A₀,B₀,C₀)` of τ′₀, whose discriminant
`D₀ < 0` therefore satisfies `t_m² − 4m = λ_m² D₀` for m = 41, 43, 61. The finite
enumeration (§2, re-proved by `decide`) forces **`D₀ = −163`**.

**(C6) Reduction / h(−163) = 1**: any `τ′₀ ∈ ℍ` whose primitive quadratic has
discriminant −163 is Γ-equivalent to τ₁₆₃ (only reduced form: (1,1,41)). Bespoke
terminating reduction: apply `T^n` to get `|B| ≤ A`, apply `S` when `A > C`; strong
induction on A; final finite check `A ≤ 7` by `decide`/`interval_cases`.

**(C7)** Hence `x = j(τ′₀) = j(τ₁₆₃) = j₀`. Every root of `minpoly ℚ j₀` equals `j₀`;
writing `minpoly = ∏(X − rᵢ)` over ℂ (splits, Mathlib), the subleading coefficient gives
`(deg)·j₀ ∈ ℚ`, so **`j₀ ∈ ℚ`** — no separability argument needed. This is
`j_τ₁₆₃_rational`; with statement 1 and `isInt_of_integral_of_rat`, `j_τ₁₆₃_integer`.

Notes:
- Only the *ℚ-version* of Φ_m is needed for m = 43, 61 (skip (B6)–(B7) for them).
- **Trap**: the natural triple {41, 43, 47} does *not* work — `D₀ = −43` survives all
  three enumerations (§2). {41, 43, 61} is a minimal working triple. The Lean enumeration
  lemma protects against this class of error; do not change the primes without re-running it.
- This argument is classical in flavor (it is the fixed-matrix half of Weber/Masser-style
  CM reasoning; BOS 1301.5672 use the same fixed-matrix set-up) but this exact
  three-prime assembly is not bookware. **Action item before Lean work: write the paper
  proof (2–3 pages) and have it checked by a number theorist** (0.5 week, cheap
  insurance; risk of an error is low — every step above was numerically sanity-checked —
  but nonzero).

### 4.3 The valence sub-plan (`Valence.lean`)

Two independent lemmas, both reusable Mathlib-grade results:

- **Injectivity mod Γ via lattice rigidity** (avoids the valence formula entirely):
  `j τ = j τ′` ⇒ the weighted-projective pairs `(E₄³ : E₆²)` agree ⇒ (case split on
  `E₄ = 0` / `E₆ = 0` / neither, plus 4–6th-root juggling) there is `λ ∈ ℂˣ` with
  `g₂(λL_τ′) = g₂(L_τ)`, `g₃(λL_τ′) = g₃(L_τ)` (scaling laws: `Lattices.lean`, proved;
  Eisenstein↔lattice bridge: `Fourier.lean`, proved). Same `(g₂, g₃)` ⇒ same ℘: the
  Laurent coefficients of ℘ at 0 are universal polynomials in g₂, g₃ (Mathlib
  Weierstrass power-series API) ⇒ ℘ agree near 0 ⇒ agree on the common domain by the
  identity theorem (ℂ minus two countable lattices is connected) ⇒ equal pole sets ⇒
  `λL_τ′ = L_τ` ⇒ `τ′ = γτ` with `γ ∈ GL(2,ℤ)`, and `Im > 0` forces `det γ = 1`.
- **Surjectivity via open-and-closed**: `j` holomorphic nonconstant ⇒ `j(ℍ)` open
  (Mathlib open mapping theorem). Closed: if `j(τ_n) → w`, move `τ_n` into the closed
  fundamental domain `𝒟` (`exists_smul_mem_fdo` + invariance); `|1728J| > 0.737/|q|` on
  `Im τ > 1.25` (**already proved in `Estimates.lean`**) bounds `Im τ_n`; the truncated
  `𝒟 ∩ {Im ≤ M}` is compact ⇒ subsequence converges in ℍ ⇒ `w ∈ j(ℍ)`. Nonempty clopen
  in connected ℂ ⇒ everything.

This is where the Isabelle development is the model; expect the injectivity half to be
the fiddlier one (root-of-unity λ bookkeeping).

### 4.4 Rejected/fallback alternatives for statement 2

- **Full Deuring conjugation route** (transport CM structure through `σ` on curve
  coefficients, classify O-lattices at h = 1): mathematically standard but needs
  uniformization of elliptic curves, `℘(αz) = R(℘ z)` as an algebra of rational maps,
  and holomorphic-endomorphism linearization (covering/lifting theory). Estimated 15–30
  weeks on its own. Keep only if 4.2's paper-proof review finds a hole.
- **Field class number via Minkowski** (`isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime`,
  bound 8.13, primes 2,3,5,7 inert — all available in Mathlib): proves h(K) = 1 nicely
  but connecting *ideal classes* to *j-values* needs the lattice–ideal dictionary, which
  the forms route skips. Not needed; noted for the record.

---

## 5. Statement 3 — s₂(τ₁₆₃) ∈ ℚ: route analysis

### 5.1 What Masser actually proves (LNM 437, Appendix One, pp. 113–122 — recovered)

**Theorem A1**: for complex-quadratic τ not Γ-equivalent to i,
`ψ(τ) := (3E₄/2E₆)(E₂ − 3/(π Im τ)) ∈ ℚ(j(τ))`. (`ψ = (3/2)s₂`; Milla Prop. 10.3 cites
exactly this.) His proof is **modular-polynomial calculus, not new elliptic-function
theory** — dependency list: Φ_D existence with **ℚ-coefficients** (no integrality, no
Kronecker congruence, no CM main theorem), an elementary matrix classification (his
Lemma A1), two Taylor coefficients of Φ_D at (j, j), and the Ramanujan derivative
identities. Steps, specialized to τ₁₆₃ (where they simplify):

1. Take the **trace-zero** fixing matrix `Λ = [[−B, −2A],[2C, B]] = [[1, −82],[2, −1]]`,
   `det Λ = 4AC − B² = 163 =: D`, `Λτ = τ`, and crucially `Λ′(τ) = D/(2Cτ+B)² = −1`.
   τ₁₆₃ is *non-special* in Masser's sense (163 ≠ 3d²), and not ~ i (or ρ):
   `E₆(τ₁₆₃) ≠ 0` (proved, `Estimates.lean`), `E₄(τ₁₆₃) ≠ 0` (from the Phase-A numerics:
   `‖1728J − (−640320³)‖ < 1` is available *without* Phase C, so `J ≠ 0, 1`).
2. `Φ₁₆₃ ∈ ℚ[X,Y]` with `Φ₁₆₃(X, j τ) = ∏_i (X − f_i τ)` — §3's (B1)–(B5) at m = 163
   (prime, so the same machinery instantiates; ~164 cosets, still abstract).
   Since Λ is primitive of det 163, `ΓΛ` is one of the cosets, so
   **`F(z) := Φ₁₆₃(j(Λz), j(z)) = 0 identically on ℍ`** — no symmetry of Φ needed with
   this argument order.
3. Expand `F` to second order at `z = τ`: with `β_{μν}` = the Taylor coefficients of
   `Φ₁₆₃` at `(j₀, j₀)` — **polynomials in `j₀` with ℚ-coefficients, hence (by
   statement 2) rational numbers** — the order-1 coefficient gives
   `(β₁₀·Λ′(τ) + β₀₁)·j′(τ) = 0`, i.e. `β₁₀ = β₀₁` (using `Λ′(τ) = −1`, `j′(τ) ≠ 0`);
   the order-2 coefficient gives Masser's (105):
   `j″(τ)/j′(τ) + 2C/(B + 2Cτ) = −j′(τ)·γ`, `γ = (β₂₀ − β₁₁ + β₀₂)/β₀₁ ∈ ℚ(j₀) = ℚ`.
4. **`β₀₁ ≠ 0`** (Masser's Lemma A1, drastically simplified at τ₁₆₃):
   `β₀₁ = ∏_{ΓC_i ≠ ΓΛ} (j₀ − j(C_i τ))`. If some other coset had `j(C_i τ) = j₀`, then
   (valence injectivity, §4.3) some `γC_i` fixes τ; matrices fixing τ form the 2-dim
   ℚ-algebra `ℚ[Λ]` (elementary 2×2 eigenvector algebra), and
   `det(aI + bΛ) = a² + 163b² = 163` forces `a = 0, b = ±1`, i.e. `γC_i = ±Λ`, i.e.
   `ΓC_i = ΓΛ`. (Cleaner than Masser's general Lemma A1; 163 squarefree does all work.)
5. Ramanujan identities (**already proved**: `deriv_E2`, `deriv_E₄`, `deriv_E₆` in
   `Ramanujan.lean`) give `j′ = −2πi·E₆·j/E₄` and the `j″/j′` formula; together with the
   elementary `(B + 2Cτ)/2C = i·Im τ` — the only place the non-holomorphic `3/(π Im τ)`
   enters — (105) becomes Masser's (106):
   **`ψ(τ) = 9 j γ + 3(7j − 6912)/(2(j − 1728))`**, manifestly in ℚ once `γ, j ∈ ℚ`.
   Hence `s₂_τ₁₆₃_rational`. (Cross-check anchor: this must be consistent with
   `s₂ = 77265280/90856689`, which Masser's own table lists as ψ = 38532540/30285553.)

Formalization shape of step 3: `F = Φ∘(j∘Λ-map, j)` with both components `AnalyticAt` at
τ (j analytic: `MDifferentiable` E₄/E₆ + nonvanishing Δ; Λ-map analytic); extract Taylor
coefficients via iterated derivs of a *bivariate polynomial composed with two analytic
germs* — contained, `deriv`-calculus-heavy, no new theory. Steps 3+5 estimated 2–3 weeks;
step 4 ≈ 1 week given §4.3; step 2 is shared infrastructure.

**Dependencies of statement 3 = statement 2 + (B1)–(B5) at m = 163 + Ramanujan
identities (done) + §4.3 injectivity + local calculus.** Note Milla's Appendix B
(`theoezweisternrest`, in progress) is the *integrality* companion (Masser's Lemma A3)
and is consumed by `Coefficients.lean`, not here; no overlap or conflict.

### 5.2 Alternative (documented fallback): division-values route at h = 1

Sketch (worked out during this survey; unrefereed): rescale to `L̂` with
`g₂(L̂) = g₃(L̂) = 27j/(j−1728) ∈ ℚ`; `℘̂(τz)` is an even elliptic function of z, hence a
rational function `R(℘̂ z)` whose coefficients can be *chosen in* `K = ℚ(√−163)` (Laurent
matching gives a K-linear system solvable over ℂ, hence over K); the denominator's root
sum gives `Σ_{v ∈ DIV(Cτ)} ℘̂(v) ∈ K`; `lemkapa1`/`lemkapa2` (App. B, in progress) turn
this into `√D·s₂·(j − 1728) ∈ K`; realness of `s₂, j` (real q, real q-expansions) plus
`√D ∈ iℝ` kills the rational part, giving `s₂ ∈ ℚ`. Pros: no Φ₁₆₃, reuses App. A/B
machinery. Cons: needs new "elliptic ⇒ rational in ℘ with coefficient-field control" and
kernel-multiplicity bookkeeping; and it is a novel argument (higher review risk). Keep as
fallback if the m = 163 instantiation of (B1)–(B5) turns out heavier than expected.
(Zagier's 1-2-3 §6.3 weight-2 trick gives only algebraicity, not ℚ(j) — insufficient.)

---

## 6. Recommended plan

### 6.1 File layout

```
Playground/Pi/SingularModuli.lean       -- keeps the 4 pinned statements; thin wrapper
Playground/Pi/SingularModuli/
  JFunction.lean        -- (B1) j·q ∈ 1 + qℤ⟦q⟧ via η-product; j(γτ) = j(τ); j analytic
  Valence.lean          -- §4.3: injectivity mod Γ (lattice rigidity), surjectivity (clopen)
  CosetOrbit.lean       -- (B2) f_i for prime m; S/T permutations; q_m-expansions in ℤ[ζ_m]
  ModularPolynomialQ.lean -- (B3)–(B5): power sums, Newton, q-expansion principle, Φ_m ∈ ℚ[X,Y]
  ModularPolynomialZ.lean -- (B6)–(B7): ℤ-coefficients (m = 41), Kronecker ±1 lemma
  QuadraticPoints.lean  -- fixed-point quadratics, content/primitivity, SL₂-conjugation, ℚ[Λ]-algebra
  FormReduction.lean    -- (C6) reduction algorithm; disc −163 ⇒ Γ-equiv τ₁₆₃; (C5) enumeration (decide)
  CMRelations.lean      -- (B8)/(C2): Φ_m(j₀,j₀) = 0 for m = 41, 43, 61 via explicit Möbius algebra
  Integrality.lean      -- (B9): isIntegral_j_τ₁₆₃
  Rationality.lean      -- (C1)–(C7): j_τ₁₆₃_rational, j_τ₁₆₃_integer
  MasserA1.lean         -- §5.1 steps 1,3,4,5: s₂_τ₁₆₃_rational
```

### 6.2 Dependency graph and execution order

```
JFunction ──► CosetOrbit ──► ModularPolynomialQ ──► ModularPolynomialZ ─► Integrality
    │                                │  │                                     ▲
    ▼                                │  └───────────► MasserA1 ◄── Ramanujan (done)
 Valence ────────────────────────────┼───────────────────┤
QuadraticPoints ── FormReduction ────┴─► Rationality ◄── CMRelations
```

Four **agent-parallelizable tracks** from day one:
- **Track 1 (keystone)**: JFunction → CosetOrbit → ModularPolynomialQ → Z. Generic in the
  prime m throughout; instantiate m = 41, 43, 61, 163 at the end.
- **Track 2**: Valence (independent of Track 1; needs only `Basic`/`Estimates`/Mathlib).
- **Track 3**: QuadraticPoints + FormReduction + CMRelations (elementary/`decide`-heavy;
  CMRelations needs only J-invariance from JFunction, available in week 1).
- **Track 4** (after ModularPolynomialQ + statement 2): MasserA1.

Do the **paper write-up of §4.2** (and a referee pass on §5.1's τ₁₆₃ simplifications)
in week 0, before committing to Tracks 2–3 details.

### 6.3 Effort estimates (focused person-weeks)

| Chunk | Estimate | Risk |
|---|---|---|
| Week-0 paper proof + review of §4.2 | 0.5 | low |
| JFunction (η-product route to ℤ-coefficients, invariance) | 2–3 | low |
| CosetOrbit (permutations, ζ_m-expansions) | 3–5 | medium |
| ModularPolynomialQ (**hardest**: (B3)–(B5)) | 3–5 | medium-high |
| ModularPolynomialZ + Kronecker | 2–3 | medium |
| Valence (injectivity 2–3, surjectivity 1–2) | 3–5 | medium |
| QuadraticPoints | 1–2 | low |
| FormReduction + enumeration | 1–2 | low |
| CMRelations (three Möbius computations + m = 163 coset id) | 1 | low |
| Integrality + Rationality assembly | 1–2 | low |
| MasserA1 (Taylor calculus 2–3, classification 0.5, formula 1) | 3–5 | medium |
| **Total** | **20–35** | |

### 6.4 Minimum viable Phase C

The single hardest **unavoidable** chunk is the q-expansion principle pipeline
(B3)–(B5) in `ModularPolynomialQ.lean` — every statement funnels through
`Φ_m(X, j τ) = ∏(X − f_i τ)` with ℚ-coefficients, and no route (including all fallbacks
except the rejected Deuring route, which is strictly larger) avoids it. Within it, the
critical lemma is:

> `Sk_eq_poly_j` : each symmetric function `S_k` of the `f_i` equals `𝒮_k(j)` for some
> `𝒮_k ∈ ℚ[X]`, proved by pole-order induction on the cusp function with coefficient
> tracking in a subring R.

Prototype this first (weeks 1–3, on a small m like 2 or 3 for testing — *not* because
small m suffices mathematically, but as a compile-time-friendly test case). If it works,
the rest of Phase C is low-variance. A useful intermediate milestone:
`isIntegral_j_τ₁₆₃` alone (Track 1 + CMRelations only, no Valence) — statement 1
end-to-end in ~10–16 weeks.

### 6.5 Decision points

1. **Week 0**: expert sign-off on §4.2's three-prime argument (else fall back to Deuring
   route and re-budget +15–30 weeks — this is the plan's main variance).
2. **q_m-expansion representation** (CosetOrbit): pairs (principal part polynomial,
   `PowerSeries ℤ[ζ_m]`) vs `LaurentSeries`. Recommend pairs; revisit if Mathlib's
   `LaurentSeries` API proves comfortable.
3. **Hecke PRs** (#40934, #41251+): if merged before CosetOrbit starts, evaluate for
   (B2)–(B3) reuse; do not wait for them.
4. **Δ-integrality route** in JFunction: η-product (recommended) vs 1728-congruence.
5. **m = 163 instantiation cost** (for MasserA1): if the generic-m machinery makes the
   164-coset instance painless (it should — nothing is per-coset), proceed; if not,
   switch statement 3 to the §5.2 division-values fallback.

### 6.6 Known traps (collected)

- **{41,43,47} fails** for (C5); use {41,43,61} and re-prove the enumeration by `decide`.
- **Split-prime double roots**: at m = 41 (or 43, 61) *two* cosets fix τ₁₆₃'s j-value, so
  `Φ_m(X,X)` has a double root at j₀ and Masser's first/second-order extraction
  degenerates. MasserA1 **must** use the trace-zero Λ with det 163 (unique fixing coset,
  `a² + 163b² = 163 ⇒ a = 0`). Conversely this doesn't matter for §§3–4 (root
  multiplicity is irrelevant there).
- Kronecker's lemma needs m non-square; the leading-coefficient root-of-unity product is
  ±1 only after using m odd (`Σ i = m(m−1)/2 ≡ 0 mod m`).
- No Galois theory on ℤ[ζ_m] coefficients: rationality must come from the power-sum
  averaging (B3), *not* from Galois descent — resist the textbook proof's structure.
- CM conventions: this project uses `A + Bτ + Cτ² = 0`, `(A,B,C) = (41,−1,1)`,
  `√D := 2Cτ + B`; Masser writes `Cτ² + Bτ + A` — translate carefully (his
  `Λ = [[−B,−2A],[2C,B]]` is stated in *his* convention; in ours it is the matrix given
  in §2).
- `UpperHalfPlane` action friction: the maps `τ ↦ (aτ+b)/(cτ+d)` for det m matrices need
  the `GL(2,ℝ)⁺` action or bespoke ℍ-endomaps; pick one early in CosetOrbit and stick to
  it (coercion churn is the main time sink in (B2)).
- The order-1 Taylor identity in MasserA1 silently uses `j′(τ₁₆₃) ≠ 0`
  (`= −2πi·E₆·j/E₄ ≠ 0`): needs `E₆ ≠ 0` (have), `E₄ ≠ 0` and `J ≠ 0` (get from the
  Phase-A/D numeric window `‖1728J + 640320³‖ < 1`, which is Phase-C-free).
- In (C7) avoid separability: extract `j₀ ∈ ℚ` from the sum of roots, not from
  irreducible-with-unique-root.

---

## 7. `PicardFuchs.lean` recommendation (off-chain `sorry`)

`exists_periods_satisfyPicardFuchs` is consumed by nothing: `Kummer.lean` proves
`SatisfiesPicardFuchs kummerB …` directly (the A7 "Ramanujan-identities" route was taken,
as PLAN.md recommended), and no other file references the theorem. Recommendation:
**drop it from the main chain** — either delete the theorem (keeping the module docstring
as a design record) or demote it to a `proof_wanted`/TODO comment, so that
`chudnovskySum_eq_pi_inv`'s dependency cone is sorry-free once Phase C and the in-progress
App. A/B sorries land. Proving it from `kummerB` (via local inversion of J on `Region`,
where `j′ ≠ 0`) is a coherent ~1–2-week exercise with zero payoff for the main theorem;
do it only if a "periods satisfy Picard–Fuchs" statement is wanted for Mathlib
upstreaming later.
