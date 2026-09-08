# Diophantine tuples

Notes and partial formalization progress for the result that there is no
Diophantine quintuple. See [Prove2me platform notes](../prove2me.md) for
onboarding, authentication, and local verification instructions.

## Existing work

- [There is no Diophantine quintuple — theorem](https://prove2.me/theorems/780bea2d-21a2-4653-82ae-842b3c4a1927).
- [Public mission](https://prove2.me/missions/24ad89a2-7d47-4d61-ba9e-f42533775072).
  As checked on 2026-09-07, the
  [proposal](https://prove2.me/my-missions/27ea4675-65a7-45ef-84fa-0db8d568e582)
  is `Reviewed`, the mission is public, and it has no curated milestones yet.
  The headline theorem remains `Open`.
- [Source paper](https://arxiv.org/abs/1610.04020v2), Section 1, Theorem 1.
  [Local TeX source](1610.04020v2.tex), downloaded unchanged from
  [arXiv v2](https://arxiv.org/src/1610.04020v2) (original filename: `Final-arxiv.tex`).

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
The classification child is now proved (see the delegated descent proof below).
The three exclusion children, including the paper's analytic arguments and
certified finite computations, remain open.

## Checked progress (2026-09-07)

The live platform now has seven direct proofs and two resolved reductions
(finite-degree existence and classification). The headline remains an accepted
conditional reduction with three open exclusions. The earlier report of six
proved targets before the descent proof overstated the count at that time.
Accepted reductions do not close their parent while imported children remain
open; the three main exclusions remain substantial unproved work.

A Lake project (`lean-toolchain`, `lakefile.lean`, Mathlib `0df444a`) lives
in `~/prove2me_workspace`. The earlier setup check
`lake build Solutions.SmokeTest` passed; it was not rerun for this review.

Direct proofs (`ACCEPTED`):

- `diophantine_triple_non_euler_lower_bound`: a non-Euler increasing triple
  satisfies `4ab<c` (Jones gap lemma). Muse Spark supplied the direct proof;
  independent local checks and server verification passed.

- `diophantine_descent_step_exists`: every non-Euler increasing Diophantine
  triple admits a positive, strictly smaller descent value and a sorted
  successor triple. Proved by Muse Spark through `pi`, independently compiled,
  and accepted by the server; see the proof record below.

- `euler_triple_square_identities`: if `a*b+1=r^2` and `c=a+b+2r`, then
  `ac+1=(a+r)^2` and `bc+1=(b+r)^2` (Section 8, `s=a+r`, `t=b+r`).
- `euler_triple_dplus_identity`: `d_+(a,b,c)=4r(a+r)(b+r)` for Euler
  triples, i.e. the Euler-quadruple extension (Section 8).
- `diophantine_degree_one_parametrization`: signed formulas over `Int`,
  `(r+sa)^2=ad+1`, `(b+sr)^2=bd+1`, `d_+(a,d,b)=4r(r+sa)(b+sr)` with
  `s=±1`, `d=a+b+2sr` (algebra used in the proof of Theorem 8).
  This proves signed polynomial identities, not that every degree-one triple
  has this parametrization; that connection and the square-root sign conditions
  remain to be established.
- `diophantine_degree_ge_two_two_steps`: degree `≥2` unfolds to two
  descent steps, by double inversion of `HasDegree` (start of Theorem 9).
- `diophantine_quintuple_sorting`: increasing relabelling of a quintuple
  via `Finset.orderEmbOfFin` (Section 10).

Reduction (`SKETCH_ACCEPTED` on the classification child
`4da04ad5-…`, submission `f0898389-…`): the classification splits into
`diophantine_quintuple_sorting` and the reusable
`diophantine_triple_finite_degree` (Proposition 3 existence). Both are now proved,
so classification has auto-resolved to `Proved`.

Further reduction (`SKETCH_ACCEPTED` on `diophantine_triple_finite_degree`,
submission `c6323185-…`): finite-degree existence splits into the
child `diophantine_descent_step_exists` (Lemma 7: a non-Euler triple takes
one descent step) plus termination by strong induction on the largest entry.
The child is now proved, so finite-degree existence has auto-resolved to `Proved`.
The graph view of `diophantine_triple_finite_degree` now shows this child
instead of an empty decomposition.

## Current dependency graph

The headline retains three exclusion branches. The degree-at-least-two branch
has an accepted reduction to eight children, of which the Jones gap lemma is
now proved. The upper-bound child has a four-child reduction, and its
irregularity child now reduces directly to the shared Fujita dependency. The
live frontier has twelve open leaves in total:

- Euler exclusion (degree zero).
- Degree-one exclusion.
- Five corrected `_quintuple` interval cases (I–V).
- [Global bound](https://prove2.me/theorems/06b8fe7b-5969-4b51-bc5c-515a705c27ad).
- [`b<2a` ratio case is impossible](https://prove2.me/theorems/aacdd6f0-17e6-4304-a005-51cf0db786eb).
- [`2a≤b≤3a` ratio case is impossible](https://prove2.me/theorems/4e990b8a-b6cf-4321-a307-169f8149c0db).
- [Fujita regularity](https://prove2.me/theorems/9268817c-4e0a-4da3-b4a4-3811702b8e72).
- [Quadruple extension criterion](https://prove2.me/theorems/a907075f-8a50-4173-949f-618bfab43bf0).

Sorting and descent-step existence are connected through the proved
classification reductions. The four earlier algebraic/two-step helpers remain
outside the accepted headline graph. More visible open leaves reflect the new
decomposition, not additional proved exclusions.

## Statement errors found in review (2026-09-07)

### Missing quintuple-extension hypotheses

All five published `diophantine_degree_ge_two_case_*` targets assume only a
Diophantine triple, degree at least two, a global numerical bound, and an
interval condition, then conclude `False`. They omit the hypothesis that the
triple extends to a quintuple. The paper excludes such extensions, not the
triples themselves. These original statements were replaced and retired on 2026-09-07; see the repair record below.

A concrete counterexample to
[Case V](https://prove2.me/theorems/a76a401f-1b38-4bd8-9df5-7098bbf5833b)
is `(a,b,c,n) = (1,3,1680,2)`:

- Pairwise products plus one are `4 = 2²`, `1681 = 41²`, and `5041 = 71²`.
- The descent is `(1,3,1680) → (1,3,120) → (1,3,8)`, ending at an Euler
  triple, so `HasDegree 1 3 1680 2` holds.
- `a*c = 1680 < 67700000000000000000000000`.
- `4*a²*b³ = 108 < 1680` and `a*c*20 = 33600 < 3609*b³ = 97443`.

This counterexample was checked with Lean 4.33.1 against the workspace's actual
`DiophantineDescent` definition. The reproducible check is in
[`review_case_five_counterexample.lean`](review_case_five_counterexample.lean):

```sh
cd ~/prove2me_workspace
lake env lean ~/gits/lean-monorepo/informal/diophantine_tuples/review_case_five_counterexample.lean
```

Repair the interval targets by retaining an ordered quintuple whose smallest
three entries are `a,b,c`, or an equivalent explicit extension hypothesis.
These erroneous targets are not imported by the accepted headline reductions,
so they do not invalidate the checked assembly.

### Gap between Cases III and IV

[Published Case III](https://prove2.me/theorems/b319a5fc-055a-41c6-9426-df53eec59d5c)
ends at `c² ≤ 16*a²*b⁵`, while
[Case IV](https://prove2.me/theorems/d2cc741a-2664-48aa-abb6-df88f1692763)
starts at `16*a³*b⁵ < c²`. For `a > 1`, this leaves a gap in the interval
coverage. In the [TeX reference](1610.04020v2.tex), the detailed Case III proof
under `\label{thm:deg2}` uses `c ≤ 4*a^(3/2)*b^(5/2)`, whose squared form is
`c² ≤ 16*a³*b⁵`. The preceding interval summary has an inconsistent exponent,
which appears to have been copied into the published target. Use the detailed
case boundary and prove that the corrected intervals cover the required range.

The source TeX is preserved unchanged. The review left the platform unchanged;
the subsequent repair below addresses both statement issues.

## Interval repair using Muse Spark (2026-09-07)

Muse Spark, invoked through the local `pi` shell wrapper, drafted corrected
statements and an elementary coverage proof. The statements were reviewed against
the originals and compiled independently with Lean 4.33.1. Because platform
formal statements cannot be edited, five replacements were published with the
suffix `_quintuple`; the original targets were retired with replacement links:

- [Case I](https://prove2.me/theorems/143f13f8-143a-47c4-95f1-0e8c8603464d).
- [Case II](https://prove2.me/theorems/ca60c3f3-bdc9-406e-9e4d-30a33362a0fd).
- [Case III](https://prove2.me/theorems/20b664aa-1d67-4836-9703-08d71c01f248).
- [Case IV](https://prove2.me/theorems/5d09b2c9-76ca-440d-bb22-ae6a9e44a70b).
- [Case V](https://prove2.me/theorems/95666c13-d5ac-4753-b42a-5d701a465b0f).

Each replacement explicitly assumes `Quintuple f`, `Ordered f`, and
`f 0 = a`, `f 1 = b`, `f 2 = c`. Case III now ends at `c² ≤ 16*a³*b⁵`.
All five remain **Open** and are now connected through the accepted
degree-at-least-two reduction recorded below.
The published payload is preserved in
[`corrected_interval_targets.json`](corrected_interval_targets.json).

[`interval_coverage.lean`](interval_coverage.lean) proves that the corrected five
intervals cover every `a,b,c` satisfying `4*a*b < c` and
`20*a*c < 3609*b³`. Independent Lean checking passed, and `#print axioms`
reports no axioms. This proves only the interval split: deriving those two
outer bounds from the number-theoretic hypotheses and excluding each case
remain obligations. This local helper has not been submitted to the platform.

```sh
cd ~/prove2me_workspace
lake env lean ~/gits/lean-monorepo/informal/diophantine_tuples/interval_coverage.lean
```

Worker task files, sessions, and reports are in `~/prove2me_workspace/work/`;
project delegation instructions are in [`AGENTS.md`](AGENTS.md).

## Delegated descent proof accepted (2026-09-07)

Muse Spark fixed its initial draft autonomously in the saved `pi` session.
The resulting [`descent_step_exists.lean`](descent_step_exists.lean) was reviewed
and independently compiled with Lean 4.33.1. Both the original theorem and the
submission renamed to `solution` compiled cleanly; their only axioms are
`propext`, `Classical.choice`, and `Quot.sound`. There are no open-theorem imports.

Submission `8da17149-f211-4741-89d0-7769d26298aa` was **ACCEPTED**. Live checks
confirmed these targets now have status `Proved`:

- [Descent-step existence](https://prove2.me/theorems/f63c39bb-6593-4289-b407-eded17381398).
- [Finite-degree existence](https://prove2.me/theorems/20d2851c-b046-4967-93c1-35a95ce3004a).
- [Classification](https://prove2.me/theorems/4da04ad5-a323-4124-a8c3-cd083a31b394).

The last two resolved through their existing accepted reductions. The headline
remains open. At that point it had three exclusion leaves; the subsequent
reduction below expands the degree-at-least-two branch.

The proof constructs the integer descent value using the Vieta square
identities, proves it is positive and less than `c`, converts its square
witnesses to natural numbers, excludes repeated entries using the fact that
`u²+1` is not a square for positive `u`, and sorts the successor triple.

Submission source: `~/prove2me_workspace/Solutions/Sol_diophantine_descent_step_exists.lean`.
Worker report: `~/prove2me_workspace/work/pi_descent_report.md`.
Server verdict and resolved-parent checks: `work/pi_descent_completion_status.json`
in that workspace. The older failed draft and diagnostics are historical only.

```sh
cd ~/prove2me_workspace
lake env lean ~/gits/lean-monorepo/informal/diophantine_tuples/descent_step_exists.lean
```

## Degree-at-least-two reduction accepted (2026-09-07)

Muse Spark assembled the corrected cases, interval coverage, and global bound,
identifying two missing source lemmas. Its initial draft declared these as
in-file axioms; that draft was not submitted. After statement review, the two
lemmas were published as open targets and the axioms were replaced with tracked
`Theorems.Thm_*` imports. The resulting reduction independently compiled.

Submission `85add35d-1bbe-4cc4-bca3-0c379b15aeb5` was **SKETCH_ACCEPTED** for
`diophantine_quintuple_degree_ge_two`. This is a conditional reduction, not a
proof of the exclusion: seven of its eight imported theorem children remain open after the Jones proof below.
Triple extraction, non-Euler status from positive degree, corrected interval
coverage, and case assembly are checked directly.

Source: [`degree_ge_two_reduction.lean`](degree_ge_two_reduction.lean).
New child payloads: [`range_bound_targets.json`](range_bound_targets.json).
The two range lemmas follow the paper's `lem:Jones` and `lem:acb`; their
statements retain the distinct triple and quintuple hypotheses respectively.

The Jones gap child was subsequently proved, as recorded below.

## Jones gap lemma accepted (2026-09-07)

Muse Spark proved the non-Euler bound `4ab<c` autonomously. Both its original
proof and the submission version independently compiled with only the axioms
`propext`, `Classical.choice`, and `Quot.sound`; there are no open-theorem imports.
Submission `66d2e188-00cb-40ec-aa7d-db13c9e29e6d` was **ACCEPTED** for
[the Jones gap lemma](https://prove2.me/theorems/54dfe43a-91ce-4dd4-af67-06cc94b8ae10).
The headline frontier consequently shrank from ten to nine open leaves.

The proof constructs the positive descent value `m`, establishes the inverse
regular-extension identity, excludes the negative extension by the strict
descent bound, and concludes `c>4abm≥4ab`. It includes its descent arguments
directly, so it is a direct proof rather than an imported reduction.

Source: [`jones_gap_bound.lean`](jones_gap_bound.lean).
Submission file: `~/prove2me_workspace/Solutions/Sol_diophantine_triple_non_euler_lower_bound.lean`.
Worker report and server verdict: `work/pi_jones_report.md` and
`work/pi_jones_verdict.json` in that workspace.

Muse Spark is now working on the remaining quintuple range upper bound
`20ac<3609b³`. Task and log: `work/pi_acb_task.md`, `work/pi_acb.log`.
No result of that new attempt is claimed yet.

## Quintuple upper-bound reduction accepted (2026-09-07)

Submission `5305b968-32a2-49ba-9290-09dce0258efc` was **SKETCH_ACCEPTED**
for the quintuple range bound `20ac<3609b³`. Muse Spark completed and locally
checked the exact reduction; Astra reviewed the statements and dependencies,
published the four children, and submitted it without duplicating Lean checks.

The four children are the `b>3a` gap, Fujita regularity, the general
Fujita–Miyazaki quadruple extension criterion, and the explicit irregularity
of `{a,b,d,e}`. The irregularity child now has an accepted direct reduction to
Fujita regularity, leaving three distinct open source leaves in this part of
the graph. The reduction proves the root comparison `d>4abc`, the two
applicable threshold cases, and the scaling/cancellation to the target bound.
At the time this reduction was accepted, the headline frontier expanded from
nine to twelve leaves because its source dependencies became visible. The
later irregularity reduction below brought the current count to eleven.

Source: [`quintuple_range_upper_reduction.lean`](quintuple_range_upper_reduction.lean).
Child payloads: [`quintuple_range_children.json`](quintuple_range_children.json).
Worker report: `~/prove2me_workspace/work/pi_acb_report.md`.
Server verdict: `work/pi_acb_verdict.json` in that workspace.

### Irregularity child reduced directly

Submission `fbf6e5de-bd23-4798-91cb-01cf0ff73860` was
**SKETCH_ACCEPTED** for the irregularity of `{a,b,d,e}`. Muse Spark found a
direct algebraic proof from Fujita regularity and the full quintuple property.
If both successive extensions were regular, then
`(d-a-b)² = ce+4ab+4`; combining this with `ce+1=w²` places `w²` strictly
between `(d-a-b-1)²` and `(d-a-b)²`, a contradiction. The `ce+1` witness is
load-bearing. The target remains open only through Fujita regularity and is no
longer an open leaf, so the headline frontier falls from twelve to eleven.

Proof: `~/prove2me_workspace/Solutions/Sol_diophantine_quintuple_abde_irregular.lean`.
Worker report and verdict: `work/pi_irregular_direct_report.md` and
`work/pi_irregular_direct_verdict.json` in that workspace.

### The `b>3a` child split by the source proof

Submission `f00c1519-b94e-4d8d-8400-e9f8e1c58ba1` was
**SKETCH_ACCEPTED** for `b>3a`. After reading Cipu–Fujita's original proof,
Muse Spark reduced it to the paper's two ratio cases: no quintuple can have
`b<2a`, and none can have `2a≤b≤3a`. These are distinct Pell-sequence and
numerical-bound arguments. Replacing one opaque leaf with the two source cases
raises the current headline frontier from eleven to twelve.

Proof: `~/prove2me_workspace/Solutions/Sol_diophantine_quintuple_b_gt_3a.lean`.
Worker report and verdict: `work/pi_b3a_report.md` and `work/pi_b3a_verdict.json`
in that workspace.

Muse Spark is now attempting the `b<2a` source case. Task/log:
`work/pi_b3a_case1_task.md`, `work/pi_b3a_case1.log`.

## Remaining work and priorities

1. Prove the remaining source leaves of the accepted quintuple range
   upper-bound reduction, starting with the two cases underlying `b>3a`; the
   irregularity child now reduces to Fujita regularity, and the Jones lower
   bound is proved.
2. Build on the proved descent and classification results to connect the
   exclusion infrastructure to the remaining three open branches.
3. Expose shared dependencies of the exclusions as precise reusable targets:
   Pell parametrizations, congruences and gap bounds (Sections 5–6), quantitative
   logarithmic estimates including the Matveev, Mignotte, and Laurent inputs
   (Section 7), and Baker–Davenport reduction (Lemma 26, Section 8).
4. Design certified finite checks, including proofs that candidate generation
   covers every possible case. The paper reports 58,258,307 Euler pairs and
   219,497,932 degree-one cases, plus the degree-at-least-two searches. Its
   reported GP computations are not Lean certificates. Search coverage and
   rigorous numerical bounds remain substantial work.
5. Extend the accepted degree-at-least-two reduction with shared infrastructure,
   connect the other exclusion branches, and curate mission milestones.

The detailed infrastructure draft remains at
`~/prove2me_workspace/work/batch2_spec.md`. Its statements and proposed checking
strategy still need review. In particular, Lemma 26 has not been published as a
Lean target; the draft identifies a continued-fraction interface issue with
Mathlib's `GenContFract` API. An adapter or a formulation using explicit
approximation bounds needs to be chosen.

## Local artifacts

This folder contains the progress notes, unchanged paper source, and review
counterexample. The formalization project remains in `~/prove2me_workspace`,
with definitions in `Definitions/`, target statements in `Theorems/`, solutions
in `Solutions/`, and planning notes in `work/`.

## Automatic Astra check-ins

A macOS LaunchAgent (`com.xuanji.diophantine-mission-checkin`) queues a check-in
for **Astra in this Codex thread every 30 minutes**, explicitly selecting
`gpt-6-astra`. Astra coordinates results and next tasks; proof development and
local Lean verification remain delegated to Muse Spark through `pi`.
The earlier pi-only supervisor was replaced; it is no longer scheduled.

Runner: `~/prove2me_workspace/work/mission_checkins/wake_astra.py`.
Instructions: `astra_prompt.md`; latest enqueue result: `status.json` in the
same directory. The actual LaunchAgent enqueue test succeeded. The Mac must
be awake and the user logged in; a busy Codex thread receives queued work when
available. Create `PAUSED` in that directory to prevent future wake-ups;
removing it resumes the schedule. Already queued messages are not cancelled.

The upper-bound exact reduction is now accepted as a sketch; see the record
above. Current worker status is recorded in `work/mission_checkins/progress.md`
in the Lean workspace.
