# Task: Verify Semantic Equivalence of Chapter {ch_num} Formalized Statements

## Objective

Verify that each formalized Lean statement in `{lean_chapter_file}` is semantically equivalent to the original LaTeX theorem/definition quote.

## Temporary Files

If you need to create any temporary or scratch files during your work, you **must** place them in:
```
{project_root}/tmp/
```
Create this directory if it does not exist. Do NOT create temporary files anywhere else in the project.

## Step 0: Coverage Check

First, run the coverage check to ensure all LaTeX theorem and definition blocks appear in the Lean file:

```bash
python {evaluation_dir}/check_coverage_latex_quote.py {theorems_and_defs_dir}/ch{ch_num}.txt {lean_chapter_file}
```

If the coverage check fails (missing blocks, duplicate blocks, or adjacency violations), report the failure and stop. The formalization step must fix these issues before verification can proceed.

The coverage checker also verifies **adjacency**: every `/-Exact quote...-/` comment block must be immediately followed by its `theorem`/`def`/`lemma`/`corollary` declaration with nothing in between (only blank lines allowed). If the checker reports adjacency violations, those must be fixed too.

## Step 1: Build Check

Run:
```bash
cd {project_root} && lake build
```

The build must complete with no errors. `sorry` is allowed since we are only checking statements.
If the build fails with errors in ch{ch_num}.lean, report the failure and stop.

## Step 2: Semantic Equivalence Check

Read `{lean_chapter_file}`.

For **each** theorem/corollary/lemma/definition (identified by the naming pattern `Ch{ch_num}_theorem_*`, `Ch{ch_num}_corollary_*`, `Ch{ch_num}_lemma_*`, `Ch{ch_num}_def_*`), verify semantic equivalence among the three representations:

1. **Exact LaTeX quote** (in the comment block starting with `--Exact quote of the latex code`)
2. **Natural language statement** (in the comment block starting with `--Natural language statement`)
3. **Lean formalization** (the actual `theorem`, `corollary`, `lemma`, or `def` statement)

### For each theorem/definition, assess:

**A. LaTeX -> Natural Language Faithfulness:**
- Does the natural language statement accurately capture the meaning of the LaTeX?
- Are all conditions, quantifiers, and logical structure preserved?
- Are there any omissions or additions?

**B. Natural Language -> Lean Faithfulness:**
- Does the Lean formalization accurately capture the natural language statement?
- Are the types correct?
- Are quantifiers (forall, exists) correctly placed?
- Are logical connectives (and, or, implies, iff) correctly used?
- Is the structure of compound statements (conjunctions of multiple parts) preserved?

**C. Overall Semantic Equivalence:**
- Rate the equivalence: **Equivalent** / **Minor discrepancy** / **Major discrepancy**
- If not equivalent, explain the discrepancy clearly

## Step 3: Write Results

Write the full verification results to: `{output_file}`

The results file must contain:

1. **Coverage check result** (pass/fail with output)
2. **Build check result** (pass/fail)
3. **Per-statement semantic equivalence assessment** (for each theorem/definition) with ratings
4. **Summary**: total statements checked, number equivalent, number with minor discrepancies, number with major discrepancies
5. **List of statements with even minor discrepancies** that need to be re-formalized

## CRITICAL: Check Original Mathlib4 Definitions

**When verifying semantic equivalence, you MUST look up the original definitions in Mathlib4 whenever the Lean formalization uses Mathlib types, structures, predicates, or constants** (e.g., `IsCompact`, `Continuous`, `Finset.sum`, `MeasureTheory.Integrable`, etc.).

Do NOT assume you know what a Mathlib definition means from its name alone. Names can be misleading, and Mathlib definitions often carry subtle conditions, bundled data, or nonstandard conventions that differ from the textbook.

**You have the `loogle_search` tool available.** Use it to search Mathlib4 lemmas and definitions by type signature or name. For example, `loogle_search("IsCompact")` or `loogle_search("Continuous, Metric.ball")`. This helps you quickly find the correct Mathlib definitions and related lemmas.

**You must:**
1. **Look up every Mathlib definition used in the formalization.** Use `loogle_search` to find the definition and its module, then read the actual Mathlib source file (use `lake env printPaths` to locate Mathlib, then read the relevant `.lean` file) to see the real definition — not just the type signature.
2. **Compare the Mathlib definition against the textbook's mathematical meaning.** Check: Does the Mathlib definition impose additional conditions? Does it generalize in a way that changes the meaning? Does it use a different but equivalent formulation?
3. **Flag any mismatch.** If the Mathlib definition does not exactly capture the textbook's intent — even subtly — report it as a discrepancy. For example: the textbook says "open set" but the formalization uses a predicate that also requires nonemptiness; or the textbook says "continuous" in a specific sense but Mathlib's `Continuous` requires a different topology.

**This is not optional.** Skipping this check is the single most common source of silently wrong formalizations. A statement that type-checks and builds is NOT necessarily semantically equivalent to the textbook — it could be trivially true, vacuously true, or state something entirely different if the Mathlib definitions don't match the textbook's intent.

## Important

- Be rigorous and mathematically precise in your assessment
- A "minor discrepancy" is a stylistic difference that doesn't change mathematical meaning
- A "major discrepancy" is a difference that changes the mathematical content of the theorem or definition
- Do NOT modify ch{ch_num}.lean yourself - only report issues
- Even minor discrepancy fail the verification!! Strict semantic equivalence is required!
