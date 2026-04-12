# Verdict Task: Chapter {ch_num} Proof Verification

Read the verification result file at `{verification_result_file}`.

## Decision Criteria

Reply with ONLY the single word **'DONE'** if ALL of the following criteria are satisfied:

1. **Build Success:** `lake build` passes without errors
2. **No Sorry:** No `sorry` found anywhere in the proofs
3. **No Illegal Axiom:** No `axiom` declarations used to circumvent proofs
4. **Coverage Check Passed:** All original textbook definitions and theorem statements are preserved (coverage script passes)
5. **All Theorems Proven:** All theorems (Ch{ch_num}_theorem_*, Ch{ch_num}_corollary_*, Ch{ch_num}_lemma_*) have complete proofs

Reply with ONLY the single word **'CONTINUE'** otherwise.

## Important

- Your response must be exactly one word: either `DONE` or `CONTINUE`
- Do not include any explanation or additional text
- If the verification result file is empty or missing, reply `CONTINUE`
- If any single criterion fails, reply `CONTINUE`
