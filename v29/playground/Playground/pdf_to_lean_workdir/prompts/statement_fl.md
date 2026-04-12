# Task: Formalize Chapter {ch_num} Theorem and Definition Statements in Lean

## Objective

Translate the theorems and definitions from `{raw_data_dir}/ch{ch_num}.txt` into Lean formalizations at `{lean_chapter_file}`.

## Input Files

- **Main content**: `{raw_data_dir}/ch{ch_num}.txt` - Contains context for Chapter {ch_num}
- **Theorems and definitions**: `{theorems_and_defs_dir}/ch{ch_num}.txt` - Contains the exact LaTeX code for all theorems and definitions that must be formalized

## Reuse definitions
{reuse_instructions}

## Output Format

For each theorem/lemma/corollary/definition in the theorems and definitions file, the output in ch{ch_num}.lean should follow this format.

**Theorem example:**

```lean
/-Exact quote of the latex code of the theorem statement (include this line)
\begin{{lemma}}\label{{lem:stronglyHenkin}}
Suppose $\exists x\, A(x)$ is an $L$-sentence and $\Gamma$~is a
consistent set of $L$-sentences.
Let $c$ be a new constant symbol, so $c\notin L$. Then
\[
\hbox{{ $\Gamma \cup \{{ A(c) \limplies \forall x\, A(x)\}}$ is consistent.}}
\]
\end{{lemma}}

Natural language statement (include this line)
Suppose ∃x A(x) is a sentence and Γ is a consistent set of sentences. Let c be a new
constant symbol not in L. Then Γ ∪ {{A(c) → ∀x A(x)}} is consistent.

Lean formalization of the natural language statement (include this line)-/
theorem Ch{ch_num}_theorem_N ... : ... := by
  sorry
```

**Definition example:**

```lean
/-Exact quote of the latex code of the definition (include this line)
\begin{{definition}}\label{{def:truthAssignment}}
A \idxem{{truth assignment}}~$\varphi$ is a mapping
\[
\varphi : \{{p_1,p_2, p_3 ,\ldots\}} \rightarrow \{{\True, \False\}}
\]
from the set of propositional variables to the set of truth
values $\True$ and~$\False$.
\end{{definition}}

Natural language statement (include this line)
A truth assignment φ is a mapping φ : {{p₁, p₂, p₃, ...}} → {{True, False}} from the set
of propositional variables to the set of truth values True and False.

Lean formalization of the natural language statement (include this line)-/
def Ch{ch_num}_def_N ... := ...
```

## Naming Convention

1. Theorems, corollaries, lemmas, and definitions should use a **shared sequential index**:
   - `Ch{ch_num}_theorem_1`, `Ch{ch_num}_def_2`, `Ch{ch_num}_corollary_3`, `Ch{ch_num}_theorem_4`, etc.
   - The index increments across all types in the order they appear in the source.

2. **One Lean statement per LaTeX quote**: If a theorem/definition has parts (a), (b), (c), you should formalize it as ONE single Lean statement that captures all parts, not multiple separate statements.

3. Helper lemmas and auxiliary definitions that you create (not from `\begin{{definition}}` blocks) do NOT use the indexed naming format.

## Additional Definitions

Check `{raw_data_dir}/ch{ch_num}.txt` for any additional definitions or context needed beyond the `\begin{{definition}}` blocks to formalize the theorems. You may add helper definitions as needed.

## Verification Criteria

Continue refining the formalization until ALL of the following criteria pass:

### Criterion 1: Compilation
```bash
cd {project_root} && lake build
```
The build must complete with no errors. `sorry` is allowed since you are only formalizing statements.

### Criterion 2: Coverage Check
```bash
python {evaluation_dir}/check_coverage_latex_quote.py {theorems_and_defs_dir}/ch{ch_num}.txt {lean_chapter_file}
```
Must show:
- **100% coverage** - every theorem and definition block from the theorems and definitions file must appear in the Lean file
- **No duplicates** - each block must appear exactly once

### Criterion 3: Semantic Equivalence

For **each theorem/corollary/lemma/definition** in the file, verify semantic equivalence among three representations:

1. **Exact LaTeX quote** (in the comment block starting with "Exact quote of the latex code")
2. **Natural language statement** (in the comment block starting with "Natural language statement")
3. **Lean formalization** (the actual `theorem`, `corollary`, `lemma`, or `def` statement)

#### For each theorem/definition, assess:

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
- If not equivalent, explain the discrepancy

## Mathlib Imports

Start with these standard imports:
```lean
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
```

Add additional imports as needed for specific mathematical concepts. This repo has Mathlib4 as dependency. Feel free to use it if you have to.

## Loogle: Mathlib Lemma Search Tool

You have access to a `loogle_search` tool that searches Mathlib4 lemmas by type pattern. Use it when you need to find the right Mathlib type, definition, or lemma for your formalization.

**Example uses during statement formalization:**
- `loogle_search("Decidable, Prop")` — find how decidability is handled in Mathlib
- `loogle_search("Finset, Bool")` — find Finset operations for Boolean-valued functions
- `loogle_search('"truth_table"')` — search by name substring

Use this tool proactively when you're unsure which Mathlib type or definition best matches a concept from the textbook.

## CRITICAL: Do NOT break apart the comment-block / statement unit

Each textbook theorem or definition is a single contiguous unit consisting of:
1. The `/-...-/` comment block (LaTeX quote → natural language → "Lean formalization of the natural language statement")
2. The Lean `theorem` / `def` / `lemma` / `corollary` statement immediately after the closing `-/`

**These two pieces must ALWAYS stay directly adjacent — NOTHING may be inserted between them. No comments, no helper lemmas, no `--` lines, no doc-comments, no section headers. The ONLY thing allowed between the closing `-/` and the declaration keyword is blank lines.**

Correct:
```lean
/-Exact quote of the latex code ...
...
Lean formalization of the natural language statement-/
theorem Ch{ch_num}_theorem_1 ...
```

WRONG (comment inserted between `-/` and declaration):
```lean
/-Exact quote of the latex code ...
...
Lean formalization of the natural language statement-/
-- Helper for the next theorem    ← THIS IS WRONG
theorem Ch{ch_num}_theorem_1 ...
```

If you need to add helper lemmas, auxiliary definitions, section comments, or any other code, place them **before** the comment block or **after** the full Lean statement — **never** between the closing `-/` and the declaration. The coverage checker enforces this and will fail if anything appears between them.

## Important, you always have to pass all the Verification Criteria before you stop working!
## Put all the verification efforts you've done and verification output in the round-specific status file: `{status_file}`.
## Do not overwrite previous rounds' logs. Each round has its own directory.
## Even verification fail, still log the output and efforts.
## If you undergo formalizing-verification-formalizing-verification loop several time, that's good! Faithfully record all your verification efforts!
## Verification must contain three parts: run check coverage python check, check semantic equivalence, and lake build (sorry is ok, don't need to fill proofs).
