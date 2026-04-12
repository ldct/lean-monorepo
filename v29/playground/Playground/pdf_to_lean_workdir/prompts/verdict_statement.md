# Verdict Task: Chapter {ch_num} Statement Formalization

Read the verification result file at `{verification_result_file}`.

## Decision Criteria

Reply with ONLY the single word **'DONE'** if ALL of the following criteria are satisfied:

1. **Build Success:** `lake build` passes without errors (sorry is allowed)
2. **Coverage Check Passed:** All LaTeX theorem and definition blocks from theorems_and_defs/ch{ch_num}.txt appear exactly once in ch{ch_num}.lean (100% coverage, no duplicates)
3. **Semantic Equivalence:** ALL theorems and definitions have **Equivalent** or **Minor discrepancy** ratings - NO **Major discrepancy** found
4. **No Missing Statements:** Every theorem/corollary/lemma/definition from the source has a corresponding Lean formalization

Reply with ONLY the single word **'CONTINUE'** otherwise.

## Important

- Your response must be exactly one word: either `DONE` or `CONTINUE`
- Do not include any explanation or additional text
- If the verification result file is empty or missing, reply `CONTINUE`
- If any single criterion fails, reply `CONTINUE`
