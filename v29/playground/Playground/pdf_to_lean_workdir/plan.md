# Test Run Plan: pdf_to_lean on first 8 pages of Borcherds' Algebra Notes

**Source PDF:** https://web.ma.utexas.edu/users/vandyke/notes/250a_notes/main.pdf
**Pages:** 1-8 (title, TOC pp1-5, intro p6, Chapter 1 definitions pp7-8)
**Math content:** 9 definitions + 2 theorems from Section 1.1 (Groups: Definitions)

## Current State

- [x] Repository cloned and copied to working directory
- [x] Python venv created at `.venv/` with `agent-framework`, `pyyaml`, `pymupdf`
- [x] `config.yaml` set to `provider: "subscription"` (Claude Max)
- [x] PDF downloaded as `textbook_first8.pdf`
- [x] `extracted_latex/ch1.txt` manually created (PDF-to-LaTeX agent had buffer issues)
- [x] LaTeX validation passed (9 defs, 2 theorems, 2 proofs)
- [x] Scaffold created at `lean_formalization_output/`
- [ ] Mathlib clone/cache download (was interrupted mid-clone)
- [ ] Statement formalization loop
- [ ] Proof search loop
- [ ] Final validation

## Bug Fix Applied

`pdf_to_latex/convert.py` was missing `max_buffer_size` in its Claude options, causing
`Fatal error in message reader: JSON message exceeded maximum buffer size of 1048576 bytes`.
Fixed by adding `"max_buffer_size": 1000 * 1024 * 1024` to the options dict in
`_build_claude_opts()` (line ~307), matching what `code/pipeline.py:81` already does.

## Steps to Complete the Test Run

### Step 1: Finish Mathlib cache download

The scaffold exists but Mathlib was mid-clone when interrupted. Run:

```bash
cd lean_formalization_output
lake exe cache get
```

This downloads ~2GB of prebuilt Mathlib oleans. Takes 5-10 minutes depending on network.
Verify with `lake build` (should succeed with the placeholder chapter file).

### Step 2: Run the formalization pipeline

```bash
cd /Users/xuanji/gits/lean-monorepo/v29/playground/Playground/pdf_to_lean_workdir
source .venv/bin/activate
python3 code/pipeline.py \
  --input extracted_latex \
  --output lean_formalization_output \
  --config config.yaml
```

This will:
1. **Stage 1:** Extract theorem blocks from `ch1.txt` → `natural_language/raw_data/theorems_and_defs/ch1.txt`
2. **Stage 2:** Copy raw chapter to `Formalization/utils/ch1_info.txt`
3. **Stage 3 Phase 1:** Statement formalization loop (up to 5 rounds)
   - Claude agent writes `Formalization/ch1.lean` with Lean type signatures
   - Verification agent checks semantic equivalence
   - Verdict agent decides DONE/CONTINUE
4. **Stage 3 Phase 2:** Proof search loop (up to 5 rounds)
   - Claude agent replaces `sorry` with actual proofs
   - Verification agent checks build + coverage
   - Verdict agent decides DONE/CONTINUE
5. **Stage 4:** Final validation (`lake build` + sorry/axiom count)

### Step 3: Monitor progress

```bash
# Pipeline status
cat lean_formalization_output/experiments/auto/ch1/verification_fl_statement/AUTO_RUN_STATUS.md
cat lean_formalization_output/experiments/auto/ch1/verification/AUTO_RUN_STATUS.md

# Real-time agent output
tail -f lean_formalization_output/experiments/auto/ch1/verification_fl_statement/AUTO_RUN_LOG.txt
tail -f lean_formalization_output/experiments/auto/ch1/verification/AUTO_RUN_LOG.txt

# Token usage
cat lean_formalization_output/TOKEN_USAGE.md
```

### Step 4: Inspect results

```bash
# Check final Lean file
cat lean_formalization_output/Formalization/ch1.lean

# Build check
cd lean_formalization_output && lake build 2>&1

# Sorry count
grep -n "sorry" lean_formalization_output/Formalization/ch1.lean

# Final report
cat lean_formalization_output/final_summary.md
```

## Expected Content to Formalize

From pages 7-8, the pipeline should formalize:

| # | Kind | Name | Notes |
|---|------|------|-------|
| 1 | Definition | Concrete group | Set of symmetries |
| 2 | Definition | Abstract group | Associativity, inverse, identity axioms |
| 3 | Definition | Subgroup | Subset closed under identity, composition, inverses |
| 4 | Definition | Homomorphism | f(ab) = f(a)f(b) |
| 5 | Theorem | Proposition 1.1 | Homomorphisms preserve inverses and identity |
| 6 | Definition | Isomorphism | Bijective homomorphism |
| 7 | Definition | Endomorphism | Homomorphism with same domain and codomain |
| 8 | Definition | Automorphism | Isomorphism + endomorphism |
| 9 | Definition | Left action | Group action on a set |
| 10 | Definition | G-set | Set with a group action (homomorphism to Perm(S)) |
| 11 | Theorem | Theorem 1.1 | Abstract group iff concrete group (Cayley's theorem) |

Most definitions map directly to Mathlib (`Group`, `Subgroup`, `MonoidHom`, `MulAction`, etc.).
Theorem 1.1 is essentially Cayley's theorem. Proposition 1.1 is `map_one` + `map_inv`.

## Cost Estimate

With Claude Max subscription, no API cost. Each chapter typically uses several million tokens
across all agent rounds. For 1 short chapter with 11 statements, expect ~30-60 minutes wall time.

## Alternative: Run Steps Manually (No conda)

Since we don't have conda, all shell scripts (`run.sh`, `run_formalization.sh`) fail at the
conda hook. The workaround is to call `python3 code/pipeline.py` directly with the venv
activated, as shown in Step 2 above.
