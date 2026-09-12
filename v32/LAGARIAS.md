# Lagarias elementary criterion: formalization ledger

Target: `v32/Lagarias.lean`,
`LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion`.
PR: https://github.com/ldct/lean-monorepo/pull/7
Branch: `codex/lagarias-formalization`.

**Status: incomplete. The original target still contains its original `sorry`.**
Its definition and theorem statement have not been changed. A conditional
assembly, finite experiment, or green prerequisite job is not completion.

## Active blueprint

The user supplied *Lagarias's criterion: A self-contained proof of the core
equivalence*, prepared 12 September 2026, a 32-page PDF named
`lagarias_self_contained.pdf`. Its Sections 1–11 and Appendices A–B are the
active blueprint. The manuscript describes itself as not independently
refereed or formally verified. Each statement used must be proved or matched
to a checked theorem, not silently imported as an axiom.

The original Lagarias/Robin route is historical work. The new converse uses
least common multiples and a positive Mellin-transform argument instead of
Robin's quantitative oscillation theorem. The old conditional `Reduction`
and `Oscillation` modules are retained, but their unproved Robin hypotheses
are not the dependency graph of the active proof.

**Notation warning:** in the blueprint namespace `R(x) = psi(x) - x`.
The older module `robinBound n` is `exp(gamma) * n * log(log n)` and is NOT this
prime-counting error. `g(x) = log(log x)`, `h(x) = 1/(x log x)`, and
`w(x) = (log x + 1)/(x^2 log(x)^2)` follow manuscript (3.6).
`J(x) = gamma + g(x) + h(x) R(x) - B(x)` is exactly (3.7).

## Compiler environment and trust boundary

Use `v32/playground`, pinned to Lean and Mathlib `v4.32.0`.
Repository CI supplies the compiler feedback loop. Local container execution
has been failing with transport timeouts, so a local build is not claimed.

Completed helper declarations are checked by a transitive axiom audit allowing
only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, project
axioms, or native-evaluation trust are allowed. The blueprint workflow builds
and audits each module independently and emits a compact diagnostics job.
That diagnostics job may succeed while the prerequisite job fails: read the
reported per-module results, not just its green status.

`verify_lagarias.sh --complete` checks the unchanged actual target type,
criterion definition and transitive axioms. Ordinary elaboration of the target
with a `sorry` warning does not pass the completion criterion.

## Verified milestones and their manuscript roles

All paths below are under `v32/playground/Playground/Lagarias/`.

| Blueprint material | Checked module and result |
| --- | --- |
| Section 2 harmonic comparisons | `Basic`, `Bounds`, `HarmonicBounds`: lower comparison and explicit errors, including 7*n/log n for n>=27 and 16*n/log n for n>=3. |
| (2.5), (3.6), concavity in Section 9 | `BlueprintSmoothing`: g'=h, h'=-w, supporting-line inequality for g, and an explicit logarithmic harmonic bound with constant 16. |
| Lemma 7.1 | `BlueprintLocalFactor`: 0 <= E_p(a) <= 2*p^(-a-1), from a proved logarithmic series and geometric tail bound. |
| Lemma 9.1 | `BlueprintLCM`: log(sigma(L_x)/L_x) >= B(x)-6/sqrt(x), for every real x>=4; L_x is the actual natural-number LCM. |
| Proposition 9.2, arithmetic conclusion | `BlueprintConverseBound`: the pointwise Lagarias inequality implies J(x)>=-134/sqrt(x) for every real x>=32. No RH, Mertens theorem or oscillation hypothesis is assumed. |
| First part of Lemma 3.2 | `BlueprintMertensFirst`: abs(A(x)-log x)<=7 for x>=2, from the divisor identity and elementary sum/integral estimates. |
| Equation (3.3) | `BlueprintPrimePowerSum`: a finite bijection identifies the grouped prime-power B with the von Mangoldt coefficient sum, including endpoint powers. |
| Equation (3.5), before normalization | `BlueprintMertensSecond`: B(x)=g(x)+c+E2(x), abs(E2(x))<=14/log x and E2(x)->0. The constant c is a concrete convergent integral, NOT defined to equal gamma. |
| Euler-product input to Lemma 3.2 | `BlueprintLogZeta`: an absolutely convergent real logarithmic zeta series, with its prime-power regrouping proved in the pinned Mathlib version. |
| Gamma input to Lemma 3.2 | `BlueprintGammaIntegral`: integral log(t)*exp(-t)=-gamma and v*integral_1^infty g(x)x^(-v-1)=-log v-gamma. |
| Abelian mean lemma | `BlueprintAbelian`: bounded measurable errors tending to zero have vanishing Mellin means. The endpoint-singular extension is listed as a candidate below. |
| Lemma 10.1 and positivity step | `Landau`, `LandauIntegral`, `LandauMGF`, `LandauMellin`: real convergence boundaries and the positive-transform argument. |
| Real-axis continuation, not assumed global meromorphicity | `LandauRealAxis`, `LandauMellinAxis`: real-axis analytic germs force actual convergence and analyticity of the integral on the continued half-plane, in the manuscript's x^(-s-1) convention. |
| Q's initial transform and poles | `LandauZeta`, `LandauPoles`: exact convergent Chebyshev-error Mellin identity and genuine simple poles at zeta zeros with Re<1. |
| Differential obstruction in Proposition 10.4 | `LandauDoublePole`: a pole of order m<0 becomes a pole of order m-1 in Q-Q', excluding a holomorphic second primitive. |
| Supported maxima, Section 8 prerequisites | Existing `PrimePower`, `CAThresholds`, `CAConstruction`, `CAInterpolation`, `EulerProduct`: checked local-factor algebra, construction/structure of maximizing integers, and interpolation infrastructure. |

Evidence checkpoints (imported declaration counts overlap and are not additive):

- Head `bd33d1fe88d6c2b5ceb5101135b3289ef425baa5`, run
  https://github.com/ldct/lean-monorepo/actions/runs/34675399049:
  all then-current Blueprint/Landau modules passed, including the explicit
  Proposition 9.2 bound (210 declarations in that imported prefix closure).
- Head `ea1ede5de1f32590def03413db26faf846bf2712`, run
  https://github.com/ldct/lean-monorepo/actions/runs/34676768290:
  `BlueprintMertensFirst` and `LandauMellinAxis` passed; later candidates failed.
- Head `d84de4d04b6b70f2fbe940325fa357ecaccd310d`, run
  https://github.com/ldct/lean-monorepo/actions/runs/34677672828:
  `BlueprintPrimePowerSum`, `BlueprintGammaIntegral`, `BlueprintLogZeta` passed;
  other candidate files failed and have subsequently been repaired.
- Head `69083d6bebdd0ac42383f02beefec9e6ba478ffb`, run
  https://github.com/ldct/lean-monorepo/actions/runs/34678206394:
  `BlueprintMertensSecond` and `BlueprintAbelian` passed. The endpoint-singular
  Abelian extension and log-zeta Mellin representation had local elaboration
  failures; repairs are submitted, not yet claimed verified here.

## Current candidates awaiting successful verification

- `BlueprintAbelianGeneral`: endpoint-integrable (not uniformly bounded)
  errors have vanishing Mellin means. Needed because log log x is unbounded
  near x=1; applying the bounded lemma there would be incorrect.
- `BlueprintLogZetaMellin`: the actual convergent identity
  log zeta(1+v)=v*integral B(x)x^(-v-1), with integrability and coefficient
  growth justified independently of the Mertens constant.
- `BlueprintMertensNormalization`: prove c=gamma, abs(J(x))<=22/log x and
  J(x)->0. These conclusions are not considered proved until this file and
  its entire dependency closure pass the compiler and axiom audit.
- `BlueprintSmoothingIdentity`: derive J(a)-J(b)=integral_a^b R(t)w(t) directly
  from Abel summation. This will prove improper convergence by taking limits;
  it does not assert unconditional absolute integrability of R*w.

## Remaining essential obligations

1. Finish the pending normalization and smoothing identity; prove continuity
   and the required finite-interval calculus for the exact J.
2. Establish the initial Mellin differential identity W''=Q-Q', real-axis
   continuation and removal at s=0, then apply the checked Landau and pole
   lemmas to this actual J. Match the resulting zero statement to Mathlib's
   unchanged `RiemannHypothesis`, including the functional-equation argument.
3. For the forward direction, prove the needed Hadamard factorization/growth
   and zero-mass identity, the integrated explicit formula, the RH estimates,
   and the quantitative prime-by-prime deficit in Sections 4–7. Searching for
   a file called Hadamard is not proof of these facts: Mathlib's three-lines
   theorem is not factorization, and the external PNT project's top-level
   `HadamardFactorization.lean` inspected so far is a blueprint stub.
4. Prove the fixed-point interval checker sound and verify the complete finite
   range from Section 8, including event coverage and interpolation.
5. Assemble and audit the original target without `sorry` or added hypotheses.

## Appendix B reproduction: separate from Lean proof

`v32/playground/blueprint/verify_manuscript_certificate.py` transcribes the
printed program. Run
https://github.com/ldct/lean-monorepo/actions/runs/34675077243
reproduced every mathematical output line, including the 78,801 checked
supported endpoints, final event (999961,1), and final log N lower bound
1000007.055927. The optimized Python mode was correctly rejected.

This is an integer-only reproduction, **not a Lean proof of soundness or
coverage**. The transcription has SHA-256
`050c015f4cc838d4a829bb2479cae8c26656a56cdf5d66680760e91e0ecb295a`,
which differs from the manuscript's reported source hash
`0d553520e6ce19996143452efeff452851b8547b15fd0f05743c717388dda175`.
Only the printed program was supplied; byte-for-byte identity with an original
Python attachment has not been established.

The older `FiniteRange.lean` through 5040 was failing during ordinary `decide`
unfolding. It now uses `decide +kernel`, not native evaluation; successful
completion of this larger reduction has not yet been observed. The separate
main helper workflow is therefore not reported as green.
