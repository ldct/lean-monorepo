# Lagarias elementary criterion: formalization ledger

Target: `v32/Lagarias.lean`,
`LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion`.
PR: https://github.com/ldct/lean-monorepo/pull/7
Branch: `codex/lagarias-formalization`.

**Status: incomplete. The original target still contains its original `sorry`.**
Its definition and theorem statement have not been changed. A conditional
assembly, finite experiment, or green prerequisite job is not completion.
The current instruction is to continue updating the PR until that exact target
is solved, and to explain any genuine blocker rather than conceal it.

## Active blueprint

The user supplied *Lagarias's criterion: A self-contained proof of the core
equivalence*, prepared 12 September 2026, a 32-page PDF named
`lagarias_self_contained.pdf`. Sections 1–11 and Appendices A–B are the active
blueprint. Its specialized claims must be proved, not presumed as axioms.

The original Lagarias/Robin route is historical work. The active converse
uses least common multiples and a positive Mellin transform, not Robin's
quantitative oscillation theorem. Existing conditional `Reduction` and
`Oscillation` lemmas do not discharge the active proof obligations.

In the blueprint namespace `R(x)=psi(x)-x`, not the older `robinBound n`.
The functions `g(x)=log(log x)`, `h(x)=1/(x log x)`,
`w(x)=(log x+1)/(x^2 log(x)^2)` and
`J(x)=gamma+g(x)+h(x)R(x)-B(x)` are the manuscript's exact functions.

## Compiler environment and trust boundary

Use `v32/playground`, pinned to Lean and Mathlib **v4.32.0**.
Repository CI supplies compiler feedback. Local container execution still
fails with transport timeouts; no successful local build is claimed.
Connector commits and CI builds remain available, so this is not a reason to
stop the formalization.

Completed declarations pass a transitive axiom audit allowing only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, project axioms,
or native-evaluation trust is allowed. The blueprint workflow builds and
audits each module separately. Its compact diagnostics job can be green while
some reported module failed; read the actual per-module results.

`verify_lagarias.sh --complete` checks the unchanged actual target type,
criterion definition, and transitive axioms. Mere elaboration with a `sorry`
warning is not completion.

## Verified manuscript milestones

Project module paths are under `v32/playground/Playground/Lagarias/`.

| Manuscript component | Compiler-checked and transitively audited result |
| --- | --- |
| Section 2 | `Basic`, `Bounds`, `HarmonicBounds`: harmonic comparisons and explicit upper errors. |
| (2.5), (3.6), Section 9 concavity | `BlueprintSmoothing`: g'=h, h'=-w, tangent bound for g, and the logarithmic harmonic estimate with constant 16. |
| Lemma 7.1 | `BlueprintLocalFactor`: 0<=E_p(a)<=2*p^(-a-1), using proved logarithmic series and tails. |
| Lemma 9.1 | `BlueprintLCM`: log(sigma(L_x)/L_x)>=B(x)-6/sqrt(x) for real x>=4 and the actual natural-number LCM. |
| Proposition 9.2 | `BlueprintConverseBound`: the pointwise Lagarias inequality implies J(x)>=-134/sqrt(x) for every real x>=32. No RH, Mertens, or oscillation hypothesis is assumed. |
| Equation (3.3) | `BlueprintPrimePowerSum`: exact finite prime-power/von-Mangoldt regrouping, including endpoints. |
| Lemma 3.2, first estimate | `BlueprintMertensFirst`: abs(A(x)-log x)<=7 for x>=2. |
| Equation (3.5) | `BlueprintMertensSecond`: concrete integral constant c, B(x)=g(x)+c+E2(x), abs(E2(x))<=14/log x, and E2(x)->0. |
| Logarithmic zeta series | `BlueprintLogZeta`: absolute convergence and equality with real log zeta on the real half-line >1. |
| Mellin representation in Lemma 3.2 | `BlueprintLogZetaMellin`: log zeta(1+v)=v*integral_1^infty B(x)x^(-v-1), with convergence justified independently of c. |
| Gamma integral | `BlueprintGammaIntegral`: integral log(t)*exp(-t)=-gamma and the exact Mellin integral of g. |
| Abelian limits | `BlueprintAbelian`, `BlueprintAbelianGeneral`: vanishing Mellin means, including errors with an integrable lower-endpoint singularity. |
| **Normalization c=gamma** | **`BlueprintMertensNormalization`: the concrete c is proved equal to Mathlib's Euler constant; abs(J(x))<=22/log x and J(x)->0.** |
| Lemma 3.3, finite intervals | `BlueprintSmoothingIdentity`: J(a)-J(b)=integral_a^b R(t)w(t), proved by endpoint-exact Abel summation. |
| **Lemma 3.3, improper integral** | **`BlueprintJIntegral`: continuity of J on every interval above 2 and convergence of the finite integrals to J(a). No unconditional absolute integrability of R*w is asserted.** |
| Equation (10.8) | `BlueprintJIntegral`: absolute convergence of the actual J Mellin integral for every positive real exponent, and v*integral J(x)x^(-v-1)->0 as v decreases to 0. |
| Prime-power endpoint calculus | `BlueprintJRightDerivative`: the actual right derivative of J is -R*w at every x>=2, derived from right continuity of the endpoint-inclusive Chebyshev sum. |
| Lemma 10.1 | `Landau`, `LandauIntegral`, `LandauMGF`, `LandauMellin`: convergence boundaries and the positive-transform argument. |
| Positivity upgrade from real-axis germs | `LandauRealAxis`, `LandauMellinAxis`: actual convergence and analyticity throughout the continued half-plane. Global meromorphic continuation of J-hat is not assumed. |
| Initial Q transform and poles | `LandauZeta`, `LandauPoles`: convergent Chebyshev-error Mellin identity and simple poles at zeta zeros with Re<1. |
| Proposition 10.4 pole obstruction | `LandauDoublePole`: negative order m in Q becomes order m-1 in Q-Q'. |
| Supported-maxima prerequisites | `PrimePower`, `CAThresholds`, `CAConstruction`, `CAInterpolation`, `EulerProduct`: checked local-factor and interpolation infrastructure. |

Recent evidence (prefix-closure counts overlap and must not be added):

- Run https://github.com/ldct/lean-monorepo/actions/runs/34680748865 checked
  `BlueprintMertensNormalization` and `BlueprintSmoothingIdentity` successfully.
- Run https://github.com/ldct/lean-monorepo/actions/runs/34682031072 checked
  `BlueprintJIntegral` (360 prefix declarations) and
  `BlueprintJRightDerivative` (366 prefix declarations). Its new
  `BlueprintMellinCalculus` candidate failed and has since received repairs.
- Run https://github.com/ldct/lean-monorepo/actions/runs/34682636593 reconfirmed
  the previously checked modules; the new Mellin and zeta-real candidates had
  local elaboration failures. Repairs have been submitted and are not yet
  recorded as successful here.

## Hadamard prerequisites: source-vendored and verified

The earlier inspection of the external project's top-level blueprint stub
was not a complete search. A substantive proof development was found under
`PrimeNumberTheoremAnd/Mathlib/`.

A **61-module minimal source closure** from
`AlexKontorovich/PrimeNumberTheoremAnd` at the fixed commit
`a5154676af9aa3095150ee410cdda80555aa0642` compiled **without changing the
project's Lean/Mathlib 4.32.0 pin**. The following actual capstones passed the
standard-axioms-only transitive audit:

- `riemannXi_entireOfOrderAtMost_one`
- `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq`
- `riemannXi_hadamard_factorization_no_monomial`
- `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum`

Compatibility evidence:
https://github.com/ldct/lean-monorepo/actions/runs/34681444960

The exact source bytes, original author/copyright notices, Apache-2.0 license,
per-module SHA-256 provenance, and audit report are now committed under
`v32/playground/PrimeNumberTheoremAnd/`. The existing package declares this
minimal source library; it does not require the whole external project or its
unrelated packages. Import publication was verified in run
https://github.com/ldct/lean-monorepo/actions/runs/34682031125
and committed as `7019fa525dd39fcfa98363b33d8b351a4e8cf453`.
The temporary write-enabled import workflow was removed after success.

These results supply the general factorization and xi growth inputs. They
are not yet the manuscript's zero-mass identity or integrated explicit formula.

## Current candidates awaiting successful verification

- `BlueprintMellinCalculus`: logarithmic differentiation and analyticity of
  actual truncated Mellin integrals from polynomial bounds.
- `BlueprintMellinOperations`: explicit absolute convergence, linearity, and
  entire finite-cutoff correction transforms.
- `BlueprintZetaReal`: real-axis zeta nonvanishing from the proved Abel
  continuation formula.
- `BlueprintZetaRegular`: analytic removal of Q's apparent pole at zero,
  using a genuine entire pole-removed zeta function.
- `BlueprintXiZeros`: the actual multiplicity-indexed xi zeros, their closed
  strip, inverse-square summability, and connection to Mathlib's exact RH.

## Remaining essential obligations

1. Complete the actual Mellin differential identity W''=Q-Q', continue the
   smoothed transform along the real axis, remove its apparent singularity at
   zero, and connect the checked positivity and pole lemmas to this J.
2. Derive the zero-mass identity and integrated explicit formula, the RH
   estimates, and the quantitative prime-by-prime deficit in Sections 4–7.
3. Prove and kernel-check the complete finite certificate, including event
   coverage and supported-maxima interpolation, not just the listed endpoints.
4. Assemble and audit the original target without `sorry` or added hypotheses.

## Appendix B reproduction: separate from Lean proof

`v32/playground/blueprint/verify_manuscript_certificate.py` transcribes the
printed program. Run
https://github.com/ldct/lean-monorepo/actions/runs/34675077243
reproduced every mathematical output line: 78,801 checked supported endpoints,
last event (999961,1), final log N lower bound 1000007.055927.
Optimized Python mode was correctly rejected.

This is an integer-only reproduction, **not a Lean proof of soundness or
coverage**. The transcription's SHA-256 is
`050c015f4cc838d4a829bb2479cae8c26656a56cdf5d66680760e91e0ecb295a`,
not the manuscript's printed source hash
`0d553520e6ce19996143452efeff452851b8547b15fd0f05743c717388dda175`.
Byte-for-byte identity with an original Python attachment is not established.

The older `FiniteRange.lean` through 5040 uses `decide +kernel`, never native
evaluation. Its monolithic reduction has not yet completed in an observed
uncancelled main helper run. This smaller check is not a substitute for the
manuscript's full finite range through log N>10^6.
