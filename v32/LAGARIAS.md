# Lagarias elementary criterion: formalization ledger

Target: `v32/Lagarias.lean`,
`LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion`.

**Status: incomplete.** The original theorem still contains its `sorry`.
No conditional theorem, finite computation, or numerical experiment is a replacement
for the requested equivalence. Preserve the original definitions and theorem type.

## Environment

Use `v32/playground`, which pins Lean and Mathlib to `v4.32.0`.
Build the Lagarias modules explicitly rather than the unrelated playground library.
The target outside the package can be checked with `lake env lean ../Lagarias.lean`.

## Proof dependency graph

Primary reference: Jeffrey C. Lagarias, *An Elementary Problem Equivalent to the
Riemann Hypothesis*, https://arxiv.org/abs/math/0008177, Section 3.
Write `H(n) = harmonic n`, `gamma = Real.eulerMascheroniConstant`,
`S(n) = H(n) + exp(H(n)) * log(H(n))`, and
`R(n) = exp(gamma) * n * log(log n)`.

1. **Harmonic estimates (Lagarias Lemma 3.1).** Establish
   `R(n) <= exp(H(n)) * log(H(n))` for `n >= 3`.
   Mathlib's `NumberTheory/Harmonic/EulerMascheroni.lean` already proves
   `gamma < H(n) - log n` for positive `n`, the opposite shifted-log bound,
   positivity bounds for `gamma`, and convergence to `gamma`.
   Reuse these proofs instead of redoing the improper-integral construction.
2. **Upper error bound (Lemma 3.2).** Establish an eventual bound
   `S(n) <= R(n) + K * n / log n` for some fixed positive constant `K`.
   The paper gives `K = 7` for `n >= 20`; the reverse implication needs only
   an eventual estimate, so a larger rigorously proved constant is acceptable.
3. **Finite check.** Prove the original pointwise inequality for
   `1 <= n <= 5040`, with equality at `1`. Use exact rational certificates
   and proved bounds for exp/log; floating-point checks are not proofs.
4. **Robin, forward direction (Proposition 3.1).** From the actual Mathlib
   `RiemannHypothesis`, prove `sigma(1,n) <= R(n)` for `n >= 5041`.
5. **Robin, oscillation direction (Proposition 3.2).** From the negation of
   the actual Mathlib `RiemannHypothesis`, obtain `C > 0`, `0 < beta < 1/2`,
   and arbitrarily large integers `n` with
   `R(n) + C * n * log(log n) / (log n)^beta <= sigma(1,n)`.
6. **Asymptotic comparison and assembly.** The positive error in (5)
   eventually exceeds the error in (2). Combine (1), (3), (4) for the forward
   implication and (2), (5) for the reverse implication.

The bare Robin equivalence alone is NOT enough for the reverse direction by a
pointwise comparison: the Lagarias right-hand side is larger. The quantitative
oscillation result must be proved or replaced by another complete argument.

## Literature dependencies to audit

Lagarias attributes (4) to Guy Robin, *Grandes valeurs de la fonction somme des
diviseurs et hypothese de Riemann*, J. Math. Pures Appl. (9) 63 (1984), 187–213,
Theorem 1. He attributes (5) to Proposition 1 of Section 4 of that paper,
using work of Nicolas and Landau. These citations identify mathematical proof
obligations; they are not Lean axioms and are not presumed present in Mathlib.

## Acceptance criteria

- The target definition and theorem signature are unchanged.
- All helper modules compile with the pinned toolchain.
- Every completed milestone has a transitive axiom audit allowing only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No project axioms, `sorryAx`, or native-evaluation trust are allowed in the
  final dependency closure.
- The final target is explicitly built and audited; an ordinary successful
  `lake build` that tolerates `sorry` does not establish completion.

## Progress

- [x] Read the exact target and pinned package configuration.
- [x] Read Section 3 of Lagarias and separate the Robin dependencies.
- [x] Identify existing Mathlib harmonic/Euler–Mascheroni estimates.
- [ ] Establish a compiler feedback loop for this branch.
- [ ] Prove and audit the harmonic lower comparison.
- [ ] Prove and audit an eventual upper error bound.
- [ ] Prove and audit the finite range through 5040.
- [ ] Prove Robin's forward bound.
- [ ] Prove Robin's quantitative oscillation result.
- [ ] Assemble and audit the unchanged target without `sorry`.

Compiler status at initialization: no Lean executable is installed in the local
working container, and direct network access from that container fails DNS.
Uncompiled candidate code must be labeled as such until actual compiler output
is obtained. Updates to this ledger and the draft PR should distinguish proved,
compiler-checked, and still-open milestones.
