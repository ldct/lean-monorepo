# Lean 4 Proof Verification Task: Chapter {ch_num}

## Overview

You are a Lean 4 expert and mathematical logic reviewer tasked with verifying the formalization of Chapter {ch_num} theorems and definitions.

## File to Verify

```
{lean_chapter_file}
```

## Temporary Files

If you need to create any temporary or scratch files during your work, you **must** place them in:
```
{project_root}/tmp/
```
Create this directory if it does not exist. Do NOT create temporary files anywhere else in the project.

## Verification Tasks

You must perform ALL of the following verification checks:

## Suggest in the md file to use existing related Mathlib4 file to help with the proof.

---

### 1. Build Verification

Run:
```bash
cd {project_root} && lake build
```

**Check for:**
- Build succeeds without errors
- No compilation warnings

**Record:** Full build output, success/failure status

---

### 2. Sorry and Axiom Check

Scan the file `{lean_chapter_file}` for:

#### 2a. `sorry` Usage
Search for any occurrence of `sorry` in the file:
```bash
grep -n "sorry" {lean_chapter_file}
```

**Criteria:** There must be NO `sorry` anywhere in the file.

#### 2b. `axiom` Usage
Search for any `axiom` declarations used to avoid proving:
```bash
grep -n "^axiom\|^  axiom" {lean_chapter_file}
```

**Criteria:** There must be NO `axiom` declarations that circumvent proofs.

---

### 3. Coverage Check (Statement Preservation)

Run the coverage verification script:
```bash
python3 {evaluation_dir}/check_coverage_lean_statement.py \
  {intermediate_dir}/ch{ch_num}_specs.lean \
  {lean_chapter_file}
```

**Purpose:** This verifies that all original textbook definitions and theorem statements remain unmodified.

### 4. Adjacency Check

Run the LaTeX coverage checker (which includes an adjacency check):
```bash
python3 {evaluation_dir}/check_coverage_latex_quote.py \
  {intermediate_dir}/../../../natural_language/raw_data/theorems_and_defs/ch{ch_num}.txt \
  {lean_chapter_file}
```

**Purpose:** Verifies that every `/-Exact quote...-/` comment block is immediately followed by its `theorem`/`def`/`lemma`/`corollary` declaration with nothing in between (only blank lines allowed). No `--` comments, no helper lemmas, no doc-comments may appear between the closing `-/` and the declaration.

---

## Output Requirements

Write ALL verification results to: `{output_file}`

### Output Format

```markdown
# Chapter {ch_num} Proof Verification Results

**File Verified:** {lean_chapter_file}

---

## 1. Build Verification
**Status:** [PASS/FAIL]

---

## 2. Sorry and Axiom Check
### 2a. Sorry Check
**Status:** [PASS/FAIL]
**Occurrences found:** [number]

### 2b. Axiom Check
**Status:** [PASS/FAIL]
**Occurrences found:** [number]

---

## 3. Coverage Check (Statement Preservation)
**Status:** [PASS/FAIL]

---

## 4. Adjacency Check
**Status:** [PASS/FAIL]
**Violations found:** [number]

---

## Summary
**Build:** [PASS/FAIL]
**Sorry-free:** [PASS/FAIL]
**Axiom-free:** [PASS/FAIL]
**Coverage:** [PASS/FAIL]
**Adjacency:** [PASS/FAIL]

### Overall Verdict: [PASS/FAIL]
```

## CRITICAL: Verify Semantic Equivalence Against Mathlib4 Definitions

**Before marking any proof as verified, you MUST check that the theorem statement being proved actually means what the textbook intended.** A proof that type-checks is worthless if the statement itself is wrong.

Whenever the theorem or its proof uses Mathlib types, structures, predicates, or constants (e.g., `IsCompact`, `Continuous`, `Finset.sum`, `MeasureTheory.Integrable`, etc.):

**You have the `loogle_search` tool available.** Use it to search Mathlib4 lemmas and definitions by type signature or name. For example, `loogle_search("IsCompact")` or `loogle_search("Continuous, Metric.ball")`. This helps you quickly locate the correct Mathlib definitions, their modules, and related lemmas.

1. **Look up and read the actual Mathlib4 source definition.** Use `loogle_search` to find the definition and its module, then read the actual Mathlib source file (use `lake env printPaths` to locate Mathlib, then read the relevant `.lean` file). Do NOT rely on your memory of what a Mathlib definition means — look it up.
2. **Confirm the Mathlib definition matches the textbook's mathematical intent.** Mathlib definitions often carry subtle extra conditions, use bundled structures, or generalize in ways that silently change meaning. A formalization using the wrong Mathlib concept can type-check, build, and even have a complete proof — while stating something entirely different from the textbook.
3. **If there is any mismatch, report it as a FAIL.** Even if the build succeeds and there are no `sorry`s, a semantically wrong statement means the proof is proving the wrong thing.

**This check is not optional.** It is the most important verification step. A green build with zero `sorry` does NOT guarantee correctness.

---

## Success Criteria

The verification **PASSES** only if ALL of the following are true:

1. `lake build` succeeds without errors
2. No `sorry` found anywhere in the file
3. No `axiom` declarations used to avoid proofs
4. Coverage check script passes (all statements preserved)
5. Adjacency check passes (no code between LaTeX quote comment blocks and their declarations)
6. Mathlib definitions used in the formalization are semantically consistent with the textbook's intent

### CRITICAL: Chapter Scope Rules

- **DO NOT modify any files outside of Chapter {ch_num}.**
- **When interpreting `lake build` results:** Only check for errors and warnings related to **Chapter {ch_num} files** (e.g., `ch{ch_num}.lean`).
