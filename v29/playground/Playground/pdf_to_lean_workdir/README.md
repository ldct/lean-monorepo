# Pdf_to_Lean Pipeline

Converts mathematics textbooks and papers (PDF or LaTeX) into verified Lean 4
formalizations using Claude agents orchestrated through the Microsoft Agent Framework.

The input must be a **PDF file** containing mathematical content (definitions,
theorems, lemmas, corollaries, and proofs). The pipeline extracts these into LaTeX,
then formalizes them into Lean 4.

## Installation

**Prerequisites:**

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- [lake](https://github.com/leanprover/lean4/tree/master/src/lake) (comes with Lean)
- [Claude Code CLI](https://docs.anthropic.com/en/docs/claude-code) (`>= 2.0.0`)
- Python 3.13+ with conda

**Setup:**

```bash
# Create conda environment
conda create -n agent python=3.13 -y
conda activate agent

# Install agent framework
pip install agent-framework --pre
pip install pyyaml

# Install Claude Code CLI (if not already installed)
npm install -g @anthropic-ai/claude-code

# Verify
claude --version
elan --version
```

**Configure `config.yaml`:**

Choose one of three providers — Bedrock, Anthropic API key, or Claude subscription:

```yaml
pipeline:
  max_statement_iterations: 9
  max_proof_iterations: 3
  statement_check_interval: 1

claude:
  cli_path: "claude"
  permission_mode: "bypassPermissions"

  # Choose ONE provider: "subscription", "bedrock", or "api_key"
  provider: "bedrock"

  # --- Option 1: Claude subscription (Pro/Max) ---
  # No API key needed. Model is a shorthand: "opus", "sonnet", "haiku"
  # Claude Max required for "opus". Claude Pro supports "sonnet".
  subscription:
    model: "opus"

  # --- Option 2: AWS Bedrock ---
  bedrock:
    model: "us.anthropic.claude-opus-4-6-v1[1m]"
    aws_profile: "default"

  # --- Option 3: Anthropic API key ---
  api_key:
    model: "claude-opus-4-6-20250609"
    key: ""  # paste your Anthropic API key here
```

> **WARNING — Unrestricted permissions.** The pipeline runs Claude agents with
> `permission_mode: "bypassPermissions"`, which grants the agent **full shell
> access** on the host machine without confirmation prompts. Agents can read, write,
> and delete files, execute arbitrary commands, and make network requests. Run the
> pipeline in a sandboxed environment (container, VM, or isolated user account) and
> never on a machine with sensitive data or credentials.

> **WARNING — Token costs.** Each chapter triggers multiple Claude Opus agent calls
> across statement formalization, verification, proof search, and verdict loops. A
> single chapter can consume **millions of tokens** over several rounds. A full
> textbook run can cost **hundreds of dollars** in API credits. Monitor spending via
> `TOKEN_USAGE.md` in the output directory, which updates after every agent call.
> Consider running a single chapter first to estimate costs before processing an
> entire book.

## Quick Start

**Full pipeline (PDF to Lean):**

```bash
conda activate agent
bash run.sh /path/to/textbook.pdf
```

This runs: PDF → LaTeX conversion → format validation → formalization pipeline.
If `extracted_latex/` already has `ch*.txt` files, the PDF conversion step is skipped.

**Formalization only (from pre-extracted LaTeX):**

```bash
bash run_formalization.sh extracted_latex/ lean_formalization_output/
```

The input directory must contain `ch1.txt`, `ch2.txt`, etc. — one per chapter, in
LaTeX format with `\begin{theorem}...\end{theorem}` markup.

**PDF extraction only:**

```bash
bash run_pdf_to_latex.sh /path/to/textbook.pdf
```

**Skip already-completed chapters on re-run:**

```bash
bash run_formalization.sh --skip-chapters 1
```

---

## Pipeline Architecture

```
PDF Input
  │
  ▼
Stage 0: Scaffold Lean project
  │
  ▼
Stage 1: Extract theorem/definition blocks from LaTeX
  │
  ▼
Stage 2: Copy raw chapter text to utils (proof reference)
  │
  ▼
Stage 3: Formalization (per chapter, sequential)
  ├── Phase 1: Statement Formalization Loop (up to 9 rounds)
  │     ┌─────────────────────────────────────────────┐
  │     │  Statement FL Agent → Verification Agent    │
  │     │       → Verdict Agent (DONE / CONTINUE)     │
  │     └─────────────────────────────────────────────┘
  │
  ├── Specs Snapshot (freeze verified statements)
  │
  └── Phase 2: Proof Search Loop (up to 3 rounds)
        ┌─────────────────────────────────────────────┐
        │  Proof Search Agent → Verification Agent    │
        │       → Verdict Agent (DONE / CONTINUE)     │
        │       → Statement Change Check (periodic)   │
        └─────────────────────────────────────────────┘
  │
  ▼
Stage 4: Final validation (lake build + sorry count)
  │
  ▼
Output: Verified Lean 4 project
```

### Agent Communication Model

The pipeline does **not** use the Agent Framework's workflow engine or agent-as-tool
patterns. Instead, it uses **sequential independent agent calls** orchestrated by
Python:

```
pipeline.py (Python orchestrator)
    │ spawns
    ▼
ClaudeAgent(prompt=..., tools=[loogle_search])
    │ returns text
    ▼
pipeline.py parses result, decides next step
    │ spawns next agent
    ▼
ClaudeAgent(prompt=..., tools=[loogle_search])
    ...
```

Each agent is a fresh `ClaudeAgent` instance with no shared memory. Information passes
between rounds via **files on disk** (verification results, proof status logs,
unfaithful arguments). The Python code handles all sequencing, resume logic, and
verdict parsing.

---

## Detailed Stage Descriptions

### Stage 0: Scaffold (`code/scaffold.py`)

Creates the Lean project skeleton:

```
lean_formalization_output/
├── lakefile.toml                  # copied from lean_project_template/
├── lean-toolchain                 # copied from lean_project_template/
├── Formalization.lean             # generated: "import Formalization.ch1\n..."
├── Formalization/
│   ├── ch1.lean                   # placeholder: "-- Chapter 1: placeholder"
│   ├── ch2.lean
│   ├── utils/
│   └── intermediate_files/
│       ├── ch1/
│       └── ch2/
├── natural_language/
│   └── raw_data/
│       ├── ch1.txt                # copied from input dir
│       ├── ch2.txt
│       └── theorems_and_defs/
└── experiments/auto/
    ├── ch1/
    │   ├── verification/
    │   └── verification_fl_statement/
    └── ch2/
```

Idempotent: won't overwrite existing `.lean` files. After scaffolding, the pipeline
runs `lake exe cache get` to download the prebuilt Mathlib cache.

### Stage 1: Extract Theorem Blocks (`evaluation/keep_only_theorems_and_defs.py`)

For each chapter's raw LaTeX (`ch1.txt`), this script:

1. Finds all `\begin{theorem}...\end{theorem}`, `\begin{lemma}...\end{lemma}`,
   `\begin{corollary}...\end{corollary}`, `\begin{definition}...\end{definition}`
   blocks using regex
2. Preserves `\section{}`, `\subsection{}`, `\subsubsection{}` headers
3. Sorts everything by position in the original file
4. Writes to `natural_language/raw_data/theorems_and_defs/ch1.txt`

This stripped-down file becomes the ground truth list of what must be formalized.

### Stage 2: Copy Raw Chapters to Utils

Copies raw chapter files to `Formalization/utils/ch1_info.txt`. This gives the proof
search agent access to the full chapter text including prose, proofs, and context
(not just the stripped theorems).

### Stage 3: Formalization

Each chapter is processed sequentially through two phases.

#### Phase 1: Statement Formalization Loop (`pipeline.py:413–542`)

Runs up to `max_statement_iterations` (default 9) rounds. Each round has 3 steps:

**Step 1 — Statement Formalization Agent** (`prompts/statement_fl.md`, tool: `loogle_search`)

This Claude agent:

1. Reads the raw chapter text (`raw_data/ch1.txt`) and the extracted theorems
   (`theorems_and_defs/ch1.txt`)
2. Writes/edits `Formalization/ch1.lean` with Lean 4 type signatures
3. For each theorem/definition, produces a structured comment block:
   ```lean
   /-Exact quote of the latex code of the theorem statement
   \begin{theorem}...actual LaTeX...\end{theorem}

   Natural language statement
   The English translation of the theorem...

   Lean formalization of the natural language statement-/
   theorem Ch1_theorem_1 ... : ... := by
     sorry
   ```
4. Runs `lake build` to check compilation (`sorry` allowed)
5. Runs `check_coverage_latex_quote.py` to verify 100% coverage (every LaTeX block
   appears exactly once)
6. Self-checks semantic equivalence among the three representations (LaTeX ↔ natural
   language ↔ Lean)
7. Logs all efforts to a round-specific status file

If this is round 2+, the prompt is appended with instructions to read the previous
round's verification result and fix any major discrepancies. Reuse instructions are
injected if earlier chapters exist (e.g., "reuse definitions from ch1.lean").

**Step 2 — Statement Verification Agent** (`prompts/statement_verify.md`, tool: `loogle_search`)

An independent Claude agent (separate context, no memory of Step 1) that:

1. Runs `check_coverage_latex_quote.py` — verifies every LaTeX theorem/def block
   appears in the `.lean` file
2. Runs `lake build` — verifies compilation
3. For each formalized statement, performs a three-way semantic equivalence check:
   - LaTeX → Natural Language faithfulness
   - Natural Language → Lean faithfulness
   - Overall rating: **Equivalent** / **Minor discrepancy** / **Major discrepancy**
4. Looks up actual Mathlib4 source definitions using `loogle_search` + reading source
   files to verify types match textbook intent
5. Writes results to `round_N/fl_statements_verification_result.md`

**Step 3 — Verdict Agent** (`prompts/verdict_statement.md`)

A lightweight Claude call that reads the verification result and outputs exactly one word:

- **DONE** if: build passes + 100% LaTeX coverage + no duplicates + zero major
  discrepancies
- **CONTINUE** otherwise

The verdict is parsed by `run_agent_for_verdict()` which scans from the bottom of the
response. If **DONE**, Phase 1 ends with status FINISHED. If **CONTINUE**, the loop
proceeds to the next round. If max iterations are reached, Phase 1 ends with STOPPED.

#### Specs Snapshot (`pipeline.py:733–741`)

Between Phase 1 and Phase 2, the pipeline copies `Formalization/ch1.lean` to
`Formalization/intermediate_files/ch1/ch1_specs.lean`. This frozen baseline is used
during proof search to detect if the proof agent accidentally modified a theorem
statement. Only created if it doesn't already exist (won't overwrite on resume).

#### Phase 2: Proof Search Loop (`pipeline.py:549–702`)

Runs up to `max_proof_iterations` (default 3) rounds. Each round has 3–4 steps:

**Step 1 — Proof Search Agent** (`prompts/proof_search.md`, tool: `loogle_search`, system instructions: `skill/proving_skill.md`)

This Claude agent:

1. Reads `ch1.lean` (the file with `sorry` placeholders)
2. Reads the full chapter text from `Formalization/utils/ch1_info.txt` for original
   proofs written by the textbook author
3. If round 2+, reads previous round's `fl_proof_status.md` and
   `fl_proof_verification_result.md` to learn what strategies failed
4. For each theorem, replaces `sorry` with an actual Lean 4 proof
5. Uses `loogle_search` to find Mathlib lemmas by type signature
6. After each proof, runs `lake build` and `check_coverage_lean_statement.py` (specs
   snapshot vs current file)
7. **Forbidden from modifying theorem statements or textbook definitions** — if it
   finds one is unfaithful, it appends analysis to
   `fl_statements_unfaithful_arguments.md` instead
8. Logs every attempt (success and failure) to `fl_proof_status.md`
9. For remaining `sorry`s, adds an in-file comment listing all failed approaches

The `proving_skill.md` system prompt provides a tactic quick-reference table (`ring`,
`omega`, `simp`, `linarith`, etc.) and references to deeper files
(`super_math_skill.md`, `lean_proving_advice.md`) the agent can read when stuck.

**Step 2 — Proof Verification Agent** (`prompts/proof_verify.md`, tool: `loogle_search`)

Independent Claude agent that:

1. Runs `lake build` — checks for build errors
2. `grep -n "sorry"` — must find zero occurrences
3. `grep -n "^axiom"` — must find zero occurrences
4. Runs `check_coverage_lean_statement.py` with the specs snapshot — verifies all
   original statements are preserved character-for-character
5. Verifies semantic consistency by looking up actual Mathlib4 source definitions
6. Writes results to `round_N/fl_proof_verification_result.md`

**Step 3 — Verdict Agent** (`prompts/verdict_proof.md`)

Outputs **DONE** if: build passes + zero `sorry` + zero `axiom` + coverage preserved +
all theorems proven. Outputs **CONTINUE** otherwise.

**Step 4 — Statement Change Check** (`prompts/check_statement_change.md`, periodic)

Triggered every `statement_check_interval` rounds (default: every round), but only if
`fl_statements_unfaithful_arguments.md` exists. This separate Claude agent:

1. Reads the unfaithful arguments file (written by the proof search agent)
2. For each flagged statement, independently judges whether the critique is
   mathematically valid
3. If legitimate: modifies the statement in `ch1.lean`, then versions the specs:
   - Renames `ch1_specs.lean` → `ch1_specs_0.lean`
   - Copies updated `ch1.lean` → `ch1_specs.lean` (new baseline)
4. If not legitimate: skips it
5. Logs all decisions to `fl_statements_change_history.md`

If statement changes were reviewed in the same iteration as a DONE verdict, the
verdict is overridden to CONTINUE (forces re-verification with the new baseline).

### Stage 4: Final Validation (`code/validate.py`)

Runs across all chapters:

1. `lake build` on the entire project
2. Per-chapter checks:
   - Count `sorry` occurrences (must be 0)
   - Count `axiom` declarations (must be 0)
   - Run `check_coverage_lean_statement.py` (specs snapshot preserved)
   - Run `check_coverage_latex_quote.py` (all LaTeX blocks present)
   - Count theorems, definitions, total lines
3. Writes `final_summary.md` with a markdown table of results

---

## Evaluation Scripts

Three Python scripts in `evaluation/` are used by the agents and the final validation:

| Script | Purpose | Used by |
|--------|---------|---------|
| `keep_only_theorems_and_defs.py` | Extract `\begin{theorem}...` blocks + section headers from LaTeX | Stage 1 |
| `check_coverage_latex_quote.py` | Verify every LaTeX theorem/def block appears exactly once in a target file | Statement FL, Statement Verify, Final Validation |
| `check_coverage_lean_statement.py` | Verify all Lean `theorem`/`def` signatures from specs snapshot appear unchanged in current `.lean` | Proof Search, Proof Verify, Final Validation |

**`check_coverage_latex_quote.py`**: Uses regex to extract all
`\begin{theorem}...\end{theorem}` blocks from the theorems file, then checks each
appears exactly once (substring match) in the target `.lean` file. Exit 0 = pass,
1 = fail.

**`check_coverage_lean_statement.py`**: Parses Lean files to extract statement
signatures (everything from `theorem`/`def`/`lemma` keyword up to `:=`). For
theorems/lemmas, only extracts those preceded by a `/-Exact quote of the latex
code...-/` comment block (so helper lemmas are ignored). Then checks each signature
appears exactly once in the output file. Exit 0 = pass, 1 = fail.

---

## Custom Tool: Loogle Search (`code/tools.py`)

The `loogle_search` tool is provided to all agents. It queries the
[Loogle API](https://loogle.lean-lang.org) to search Mathlib4 lemmas by type pattern.

```python
loogle_search("IsCompact, IsClosed")       # find lemmas connecting compactness and closedness
loogle_search("|- _ < _ → tsum _ < tsum _") # find lemmas by conclusion pattern
loogle_search("List.length, _ ++ _")        # find lemmas about length of appended lists
loogle_search('"comm", Mul')                # search by name substring with type filter
```

Returns up to 15 results with name, type signature, module, and doc string. The
`name` field is the exact Lean identifier usable in proofs.

---

## PDF-to-LaTeX Subsystem

**`pdf_to_latex/convert.py`**: Uses a Claude agent with a detailed system prompt to:

1. Split the PDF into 8-page chunks using `pymupdf` (the API has a ~20 image limit
   per call)
2. Read each chunk and extract theorem/definition environments
3. Write per-chapter output files (`ch1.txt`, `ch2.txt`, ...)

The system prompt enforces strict rules: only `theorem`/`lemma`/`corollary`/
`definition`/`proof` environments, no exercises, faithful transcription (no corrections),
and proper LaTeX math notation.

**`pdf_to_latex/validate_format.py`**: Validates the extracted LaTeX:

- No forbidden environments (`proposition`, `remark`, `exercise`, etc.)
- All `\begin{...}` have matching `\end{...}`
- At least one extractable theorem/definition block exists
- No exercise content

---

## Statement Faithfulness Guarantees

The pipeline uses 11 layers of checks to ensure formalized Lean statements faithfully
represent the original LaTeX theorems and remain unchanged during proof search:

| # | Layer | Stage | Description |
|---|-------|-------|-------------|
| 1 | Embedded LaTeX quotes | Statement FL | Each Lean statement has a `/-...-/` comment with the exact LaTeX quote, natural language translation, and formalization note |
| 2 | LaTeX coverage check | Statement FL/Verify | `check_coverage_latex_quote.py` verifies every LaTeX block appears exactly once in `.lean` |
| 3 | Self-check | Statement FL | The formalization agent checks three-way semantic equivalence (LaTeX ↔ NL ↔ Lean) |
| 4 | Independent verification | Statement Verify | Separate agent re-checks three-way equivalence independently |
| 5 | Mathlib definition lookup | Statement Verify | Verification agent reads actual Mathlib4 source to confirm types match textbook intent |
| 6 | Verdict gate | Statement Verdict | Requires build pass + 100% coverage + zero major discrepancies |
| 7 | Specs snapshot | Between phases | Frozen copy of verified `ch*.lean` serves as drift baseline |
| 8 | Explicit prohibition | Proof Search | Prompt forbids modifying theorem statements or textbook definitions |
| 9 | Lean statement coverage | Proof Search/Verify | `check_coverage_lean_statement.py` detects character-level changes from specs snapshot |
| 10 | Unfaithful escalation | Proof Search | Proof agent cannot fix statements; appends arguments for separate review agent |
| 11 | Proof verdict gate | Proof Verdict | Requires build pass + zero `sorry` + zero `axiom` + coverage preserved |

---

## Token Tracking

Every agent call records input/output tokens and elapsed time. Two files are written
after every call:

- `TOKEN_USAGE.md` — human-readable markdown table
- `token_usage.json` — machine-readable cumulative data

Token counts accumulate across pipeline restarts (the tracker resumes from existing
JSON).

---

## Output Structure

```
lean_formalization_output/
├── lakefile.toml
├── lean-toolchain
├── Formalization.lean                  # Root import: import Formalization.ch1 etc.
├── Formalization/
│   ├── ch1.lean                        # Formalized chapter 1
│   ├── ch2.lean                        # Formalized chapter 2
│   ├── utils/
│   │   ├── ch1_info.txt                # Raw chapter text (proof reference)
│   │   └── ch2_info.txt
│   └── intermediate_files/
│       ├── ch1/
│       │   ├── ch1_specs.lean          # Statement snapshot (current baseline)
│       │   ├── ch1_specs_0.lean        # Versioned snapshot (audit trail)
│       │   └── ch1_specs_1.lean
│       └── ch2/
├── natural_language/
│   └── raw_data/
│       ├── ch1.txt                     # Raw LaTeX
│       └── theorems_and_defs/
│           └── ch1.txt                 # Extracted theorem/def blocks
├── experiments/
│   └── auto/
│       ├── ch1/
│       │   ├── verification_fl_statement/
│       │   │   ├── AUTO_RUN_LOG.txt
│       │   │   ├── AUTO_RUN_STATUS.md
│       │   │   ├── AUTO_RUN_STATUS.md.history
│       │   │   ├── round_1/
│       │   │   │   ├── fl_statements_status.md
│       │   │   │   └── fl_statements_verification_result.md
│       │   │   └── round_2/
│       │   └── verification/
│       │       ├── AUTO_RUN_LOG.txt
│       │       ├── AUTO_RUN_STATUS.md
│       │       ├── round_1/
│       │       │   ├── fl_proof_status.md
│       │       │   ├── fl_proof_verification_result.md
│       │       │   ├── fl_statements_unfaithful_arguments.md
│       │       │   └── fl_statements_change_history.md
│       │       └── round_2/
│       └── ch2/
├── token_usage.json
├── TOKEN_USAGE.md
└── final_summary.md
```

**Key files to inspect:**

| File | What it tells you |
|------|-------------------|
| `AUTO_RUN_STATUS.md` | Current phase, iteration, and status (RUNNING/FINISHED/STOPPED) |
| `fl_statements_verification_result.md` | Per-statement semantic equivalence ratings |
| `fl_proof_verification_result.md` | Per-theorem proof status (proved / sorry / error) |
| `fl_proof_status.md` | Proof search agent's log of every approach tried |
| `fl_statements_unfaithful_arguments.md` | Statements flagged as unfaithful by proof agent |
| `fl_statements_change_history.md` | Decisions made by the statement change check agent |
| `AUTO_RUN_LOG.txt` | Full agent output log |
| `token_usage.json` | Cumulative token usage per agent call |

---

## Log Files

The pipeline writes logs to several locations:

| Log | Location | Contents |
|-----|----------|----------|
| **Formalization agent logs** | `experiments/auto/ch*/verification_fl_statement/AUTO_RUN_LOG.txt` | Full streaming output from every statement formalization agent call |
| **Proof agent logs** | `experiments/auto/ch*/verification/AUTO_RUN_LOG.txt` | Full streaming output from every proof search agent call |
| **PDF conversion logs** | `pdf_to_latex/log/convert_<timestamp>.log` | Streaming output from the PDF-to-LaTeX agent |
| **Pipeline status** | `experiments/auto/ch*/*/AUTO_RUN_STATUS.md` | Current phase, iteration, and RUNNING/FINISHED/STOPPED state |
| **Status history** | `experiments/auto/ch*/*/AUTO_RUN_STATUS.md.history` | Timestamped progress entries across runs (including resumes) |
| **Token usage** | `TOKEN_USAGE.md` / `token_usage.json` | Per-call and cumulative token counts, elapsed time, and model name |
| **Final report** | `final_summary.md` | Build status, per-chapter sorry/axiom counts, coverage results |

To tail a running formalization in real time:

```bash
tail -f lean_formalization_output/experiments/auto/ch1/verification/AUTO_RUN_LOG.txt
```

---

## Resume Strategy

The pipeline supports resume at two levels:

**Round-level resume (automatic).** Within each chapter, both the statement
formalization loop and the proof search loop detect completed rounds by checking for
existing verification result files. On re-run, rounds that already have a non-empty
`fl_statements_verification_result.md` or `fl_proof_verification_result.md` are
skipped. The loop resumes from the first incomplete round. Token usage is also
accumulated from the previous run. If `AUTO_RUN_STATUS.md` contains "FINISHED", the
entire phase is skipped.

**Chapter-level skip (manual).** Use `--skip-chapters` to skip chapters:

```bash
bash run_formalization.sh --skip-chapters 1,2
```

**How to tell if a chapter is complete:**

Check `experiments/auto/ch*/verification/AUTO_RUN_STATUS.md` — if it says `FINISHED`,
the chapter completed successfully. Alternatively:

```bash
cd lean_formalization_output && lake build 2>&1 | grep -i sorry
```

---

## Configuration Reference

| Key | Default | Description |
|-----|---------|-------------|
| `pipeline.max_statement_iterations` | `9` | Max rounds for statement formalization loop |
| `pipeline.max_proof_iterations` | `3` | Max rounds for proof search loop |
| `pipeline.statement_check_interval` | `1` | How often (in rounds) to run the statement drift check |
| `claude.provider` | `"subscription"` | `"subscription"`, `"bedrock"`, or `"api_key"` |
| `claude.cli_path` | `"claude"` | Path to Claude Code CLI binary |
| `claude.permission_mode` | `"bypassPermissions"` | Claude Code permission mode |

---

## File Reference

| File | Lines | Role |
|------|-------|------|
| `code/pipeline.py` | 905 | Main orchestrator — runs the full pipeline |
| `code/scaffold.py` | 58 | Stage 0: Lean project setup |
| `code/validate.py` | 167 | Stage 4: final build validation |
| `code/tools.py` | 80 | Loogle search tool for Mathlib API |
| `pdf_to_latex/convert.py` | 435 | PDF → LaTeX conversion agent |
| `pdf_to_latex/validate_format.py` | 222 | LaTeX format validation |
| `evaluation/keep_only_theorems_and_defs.py` | 81 | Extract theorem blocks from LaTeX |
| `evaluation/check_coverage_latex_quote.py` | 142 | Check LaTeX block coverage |
| `evaluation/check_coverage_lean_statement.py` | 319 | Check Lean statement coverage |
| `prompts/statement_fl.md` | — | Statement formalization agent prompt |
| `prompts/statement_verify.md` | — | Statement verification agent prompt |
| `prompts/verdict_statement.md` | — | Statement verdict agent prompt |
| `prompts/proof_search.md` | — | Proof search agent prompt |
| `prompts/proof_verify.md` | — | Proof verification agent prompt |
| `prompts/verdict_proof.md` | — | Proof verdict agent prompt |
| `prompts/check_statement_change.md` | — | Statement change review agent prompt |
| `skill/proving_skill.md` | — | Proof search system instructions (tactic reference) |
| `skill/super_math_skill.md` | — | Advanced math proof strategies |
| `skill/lean_proving_advice.md` | — | Lean tactic docs and debugging tips |

---

## Troubleshooting

**`Fatal error in message reader: JSON message exceeded maximum buffer size`**

The Claude Agent SDK has a 1 MB default buffer for JSON messages from the CLI. Large
files (100KB+) can exceed this during tool use. The pipeline sets `max_buffer_size` to
1000 MB in `make_claude_options()` to avoid this. If you hit this error on an older
version of the code, update `code/pipeline.py`.

**`lake build` fails after resuming**

If a chapter was interrupted mid-edit, the `.lean` file may have syntax errors. The
proof search agent will attempt to fix these on the next run. If the file is badly
corrupted, restore from the specs snapshot at
`Formalization/intermediate_files/ch*/ch*_specs.lean` (captured after statement
formalization completes).
