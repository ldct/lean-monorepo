# Diophantine tuples

Notes and partial formalization progress for the result that there is no
Diophantine quintuple. See [Prove2me platform notes](../prove2me.md) for
onboarding, authentication, and local verification instructions.

## Existing work

- [There is no Diophantine quintuple — theorem](https://prove2.me/theorems/780bea2d-21a2-4653-82ae-842b3c4a1927).
- [Mission proposal](https://prove2.me/my-missions/27ea4675-65a7-45ef-84fa-0db8d568e582)
  for the same result. In review as of 2026-09-07; check the link for its
  current status.
- [Source paper](https://arxiv.org/abs/1610.04020v2), Section 1, Theorem 1.

## Degree-decomposition sketch (2026-09-07)

Submission `0a97e24f-549c-446a-98ea-a84f5d2c7885` on the headline theorem was
accepted as `SKETCH_ACCEPTED`. It follows the paper's final case split with four
open children:

- [Sorting and finite-degree classification](https://prove2.me/theorems/4da04ad5-a323-4124-a8c3-cd083a31b394):
  increasing relabelling plus the existence part of Section 4, Proposition 3.
- [Euler case](https://prove2.me/theorems/279fe584-d159-4e76-8f7b-10d6be65a282):
  Section 8, Theorem 7, expressed as degree zero.
- [Degree one](https://prove2.me/theorems/75070c45-eca6-4b49-951a-0cc9d5ed8961):
  Section 9, Theorem 8.
- [Degree at least two](https://prove2.me/theorems/62908dbd-6791-4a5f-bb19-d553510be7ad):
  Section 9, Theorem 9.

The shared [descent definition](https://prove2.me/theorems/90e874be-2771-40b3-b504-ab5a84bcfedc)
uses an inductive finite descent relation and sorted triples. Termination remains
an obligation of the classification child, not an assumption in the definition.
The exclusion children concern the smallest triple of an ordered quintuple.

Local source: `~/prove2me_workspace/Solutions/Sol_no_diophantine_quintuple.lean`;
supporting modules are in `Definitions/` and `Theorems/` in that workspace.
The sketch compiled locally with Lean 4.33.1 and was verified by the server.
Only the assembly is checked: all four children, including the paper's analytic
arguments and certified finite computations, remain open.

## Parallel contributions (2026-09-07)

Five parallel tracks published 12 child targets and closed 6 of them.
A Lake project (`lean-toolchain`, `lakefile.lean`, Mathlib `0df444a`) now
lives in the workspace; `lake build Solutions.SmokeTest` passes, so future
proofs can be verified locally before submission.

Direct proofs (`ACCEPTED`):

- `euler_triple_square_identities`: if `a*b+1=r^2` and `c=a+b+2r`, then
  `ac+1=(a+r)^2` and `bc+1=(b+r)^2` (Section 8, `s=a+r`, `t=b+r`).
- `euler_triple_dplus_identity`: `d_+(a,b,c)=4r(a+r)(b+r)` for Euler
  triples, i.e. the Euler-quadruple extension (Section 8).
- `diophantine_degree_one_parametrization`: signed formulas over `Int`,
  `(r+sa)^2=ad+1`, `(b+sr)^2=bd+1`, `d_+(a,d,b)=4r(r+sa)(b+sr)` with
  `s=±1`, `d=a+b+2sr` (proof of Theorem 8).
- `diophantine_degree_ge_two_two_steps`: degree `≥2` unfolds to two
  descent steps, by double inversion of `HasDegree` (start of Theorem 9).
- `diophantine_quintuple_sorting`: increasing relabelling of a quintuple
  via `Finset.orderEmbOfFin` (Section 10).

Reduction (`SKETCH_ACCEPTED` on the classification child
`4da04ad5-…`, submission `f0898389-…`): the classification splits into
`diophantine_quintuple_sorting` (now proved) and the reusable
`diophantine_triple_finite_degree` (Proposition 3 existence).

Further reduction (`SKETCH_ACCEPTED` on `diophantine_triple_finite_degree`,
submission `c6323185-…`): finite-degree existence splits into the new open
child `diophantine_descent_step_exists` (Lemma 7: a non-Euler triple takes
one descent step) plus termination by strong induction on the largest entry.
The graph view of `diophantine_triple_finite_degree` now shows this child
instead of an empty decomposition.

Still open: finite-degree existence, the five `degree_ge_two_case_*`
interval targets, `diophantine_quintuple_global_bound` (Proposition 5),
and the three exclusion leaves. Shared-cost spec (Pell machinery,
Baker–Davenport Lemma 26, certified finite checking) is drafted in
`~/prove2me_workspace/work/batch2_spec.md`; Lemma 26 is not yet a Lean
target because Mathlib's continued-fraction API is `GenContFract`-based
and needs an adapter first.
