# Lean 4 Proof Search Task: Chapter {ch_num}

## Overview

You are a Lean 4 expert tasked with proving all theorem statements in a formalization of Chapter {ch_num} of a textbook.

## Input Files

The file containing definitions and theorem statements is located at:
```
{lean_chapter_file}
```

This file contains theorems/corollaries/lemmas that need proofs, as well as textbook definitions (with LaTeX quote comments). Each theorem currently has `sorry` as its proof.

## Original Textbook Reference

The full original chapter text (extracted from the textbook PDF) is available at:
```
{proof_info_file}
```

This file contains the chapter content including definitions, theorem statements, and (when available) their original proofs as written by the textbook author. **Read this file** before starting proof search — the original proofs show how the author proved each statement, which can guide your choice of Lean tactics and proof strategy. The natural language proof is not a Lean proof, but it tells you the high-level approach (induction, contradiction, direct construction, etc.).

**Note:** Some theorems may only have statements without proofs (e.g., the textbook omitted the proof, left it as an exercise, or the proof was not extractable from the source). In those cases, you will need to construct the proof entirely on your own using mathematical reasoning and Mathlib tactics.

## CRITICAL: Round-Based Workflow — Read Previous Round, Log for Next Round

This proof search runs in multiple rounds. This is round {round_num}.

### At the START of your round:
{previous_round_instructions}
- Use this information to pick up where the previous round left off and try **different** strategies.

### At the END of your round:
- **You MUST save a complete proof status log** to `{proof_status_file}`.
- For every theorem you attempted, log **every approach you tried and why it failed or succeeded**.
- This file is the **primary way the next round learns what happened**. If you don't log your failed approaches, the next round will waste time repeating the same mistakes.

## Absolute Requirements

### DO NOT:
1. **Modify existing textbook definitions** - All definitions that have a LaTeX quote comment block (starting with "Exact quote of the latex code") must remain exactly as they are. These are textbook definitions and are immutable, just like theorem statements.
2. **Modify theorem statements** - The theorem signatures must remain unchanged, even if you think the statement is unfaithful to the latex quote.
3. **Use `sorry`** - No `sorry` may appear anywhere in the final proofs
4. **Declare axioms** - You cannot declare something as an `axiom` to avoid proving it
5. **Stop with incomplete work** - You must continue working until all theorems are proven
6. **Modify files outside Chapter {ch_num}** - Only modify `ch{ch_num}.lean` and related Chapter {ch_num} files

### You MAY:
1. Add helper lemmas to assist with proofs — **mark them `private`** (e.g. `private lemma helper_foo ...`) so they don't pollute the namespace of other files
2. Add new auxiliary definitions if needed for proofs — mark them `private` if they are only used within this chapter. However, if a definition may be reused by later chapters or extends a Mathlib concept, it can be left **public** (no `private` keyword)
3. Use Mathlib4 tactics and lemmas (the file already imports `Mathlib.Tactic`). The entire Mathlib4 is open to you.

## Loogle: Mathlib Lemma Search Tool

You have access to a `loogle_search` tool that searches Mathlib4 lemmas by type pattern. Use it when you need to find the correct Mathlib lemma name for your proof.

**Example uses during proof search:**
- `loogle_search("IsCompact, IsClosed")` — find lemmas connecting compactness and closedness
- `loogle_search("|- _ < _ → tsum _ < tsum _")` — find lemmas by conclusion pattern
- `loogle_search("List.length, _ ++ _")` — find lemmas about length of appended lists
- `loogle_search('"comm", Mul')` — search by name substring with type filter

**When to use it:**
- When `exact?` or `apply?` in Lean don't find what you need or are too slow
- When you know the shape of the lemma you need but not its name
- When a previous attempt failed because of a wrong lemma name — search for the correct one
- Use `_` as wildcards for parts you don't care about

The `name` field in results is the exact Lean identifier you can use in your proof. The `module` field tells you which import you need.

## Temporary Files

If you need to create any temporary or scratch files during your work, you **must** place them in:
```
{project_root}/tmp/
```
Create this directory if it does not exist. Do NOT create temporary files anywhere else in the project.

## Workflow

For **each theorem**, follow this process:

### Step 1: Write the Proof
Replace the `sorry` with a complete proof.

### Step 2: Build and Verify
Run:
```bash
cd {project_root} && lake build
```

**IMPORTANT: Only check errors/warnings for Chapter {ch_num} files (ch{ch_num}.lean).**

### Step 3: Check Coverage
Run:
```bash
python3 {evaluation_dir}/check_coverage_lean_statement.py \
  {intermediate_dir}/ch{ch_num}_specs.lean \
  {lean_chapter_file}
```

This script verifies that you have not modified any original theorem statements or textbook definitions. If anything is modified, **immediately revert** the changes and redo the proof.

### Step 4: Move to Next Theorem
Proceed to the next theorem after the current one passes all checks.

### If you've tried many times on a particular theorem but still fail on that, you can then try to solve other theorem, and come back to this one later.

## Logging Requirements

Log to `{proof_status_file}`:
1. all verification efforts
2. Extremely important: the methods you've tried for the theorems but failed so far!!!!!
3. the coverage score resulted from check_coverage_lean_statement.py

## Success Criteria

You are **not done** until ALL of the following are satisfied:

1. All theorems have complete proofs (no `sorry` anywhere)
2. `lake build` succeeds with no warnings
3. The coverage check script passes (no textbook definitions/theorem statements modified)

## CRITICAL: Do NOT break apart the comment-block / statement unit

Each textbook theorem or definition is a single contiguous unit consisting of:
1. The `/-...-/` comment block (LaTeX quote → natural language → "Lean formalization of the natural language statement")
2. The Lean `theorem` / `def` / `lemma` / `corollary` statement immediately after the closing `-/`

**These two pieces must ALWAYS stay directly adjacent — NOTHING may be inserted between them. No comments, no helper lemmas, no `--` lines, no doc-comments, no section headers. The ONLY thing allowed between the closing `-/` and the declaration keyword is blank lines.**

If you need to add helper lemmas or comments, place them **before** the comment block or **after** the full Lean statement — **never** between the closing `-/` and the declaration.

## During proving, if you found that a theorem statement or textbook definition is not faithful and semantically equivalent to the latex code quote, **append** your analysis and explanation to `{unfaithful_args_file}`. Include the latex quote and the current Lean statement. Then move on to other theorems. Important: don't change the statement or definition in {lean_chapter_file}, even if you think it is unfaithful to the latex code quote! Someone else will review and apply the change.

## Log the failed approach in {proof_status_file}! This helps the next round!

## If You Exit With `sorry` Still Present

If you are unable to prove a theorem and it still has `sorry` when you exit, you MUST add a comment **directly above the `sorry` in the .lean file** summarizing every approach you tried and why it failed.

Format the comment like this:
```lean
/- PROOF ATTEMPTS LOG (do not delete — helps next iteration):
  Attempt 1: Used `continuity` tactic → failed: "tactic 'continuity' failed"
  Attempt 2: Tried `apply Continuous.add` → failed: argument mismatch
  Attempt 3: Searched Mathlib for `IsCompact.of_isClosed_subset` → name doesn't exist in current Mathlib
  Key blocker: Cannot find the correct Mathlib lemma for closed-subset compactness.
-/
sorry
```

This is **in addition to** logging in `{proof_status_file}` — both places must be updated.

## Logging Examples

### Logging Example 1: Completed proof

```
## theorem_continuous_add (COMPLETED)

**Attempt 1:** Used `continuity` tactic directly → `lake build` failed with "tactic 'continuity' failed".
**Attempt 2:** Tried `apply Continuous.add` with `exact continuous_fst` and `exact continuous_snd` → `lake build` succeeded.

- lake build: success (no errors/warnings for ch{ch_num})
- Coverage check: 18/18 statements preserved (score: 100%)
- Helper lemmas added: none
- Final proof strategy: `apply Continuous.add <;> assumption`
```

### Logging Example 2: Failed/in-progress proof (CRITICAL — you MUST log every failed attempt like this)

```
## theorem_compact_subset (IN PROGRESS — NOT YET PROVEN)

**Attempt 1:** Tried `apply IsCompact.subset` with the hypothesis directly → failed: "type mismatch, expected IsCompact s, got IsCompact t".
**Attempt 2:** Tried unfolding the definition and using `Filter.Eventually` reasoning → failed: "unknown identifier 'Filter.Eventually.mono'".
**Attempt 3:** Searched Mathlib for `IsCompact.of_isClosed_subset` and applied it → failed: argument order wrong.
**Attempt 4:** Reversed argument order → `lake build` failed with "unknown identifier". Still exploring.

- lake build: still failing
- Coverage check: 18/18 statements preserved (score: 100%)
- Helper lemmas added: tried `helper_compact_inter` but it didn't help, removed it
- Proof strategy notes: The key issue is finding the right Mathlib lemma name.
```

## Before You Exit — Mandatory Logging Check

**Before you finish your session, you MUST perform the following check. Do NOT skip this.**

1. Read `{proof_status_file}`.
2. For **every** theorem you attempted (whether you succeeded or not), confirm there is a log entry. Specifically check:
   - Does the log contain an entry for each theorem you worked on?
   - For theorems you **failed** to prove: does the entry list **every** approach you tried and why it failed?
   - For theorems you **proved**: does the entry record the final strategy and build/coverage results?
3. If **any** entry is missing or incomplete, add it **now** before you exit.
4. For every remaining `sorry` in `{lean_chapter_file}`, confirm there is a comment block directly above it listing all failed approaches. If not, add it now.
