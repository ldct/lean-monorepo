================================================================================
COMPREHENSIVE LEAN 4 COMMUNITY ADVICE, TIPS, AND BEST PRACTICES
================================================================================
Compiled from: Mathematics in Lean textbook, Theorem Proving in Lean 4,
Lean community style guides, Mathlib documentation, Lean community blog,
Loogle documentation, and multiple Mathlib tactic reference pages.
================================================================================

TABLE OF CONTENTS
-----------------
1.  PROOF STRUCTURING AND ORGANIZATION
2.  TACTIC MODE VS TERM MODE
3.  ESSENTIAL TACTICS REFERENCE
4.  AUTOMATION TACTICS (Decision Procedures)
5.  SEARCH AND DISCOVERY TACTICS
6.  CALCULATIONAL PROOFS (calc blocks)
7.  CONV MODE (Surgical Rewriting)
8.  SIMPLIFICATION CONTROL (simp, simp only, simp_rw)
9.  TYPE CLASS AND INSTANCE MANAGEMENT
10. COERCIONS AND TYPE CASTING
11. WORKING WITH LOGIC (Quantifiers, Connectives)
12. WORKING WITH SETS AND FUNCTIONS
13. NUMBER THEORY PATTERNS
14. ALGEBRAIC PROOF TACTICS
15. INEQUALITY AND ORDER PROOFS
16. ANALYSIS AND TOPOLOGY PATTERNS
17. STRUCTURING LEAN FILES
18. NAMING CONVENTIONS
19. STYLE GUIDELINES
20. DEBUGGING AND ERROR MESSAGES
21. COMMON BEGINNER MISTAKES
22. ADVANCED TECHNIQUES
23. TOOL AND LIBRARY NAVIGATION

================================================================================
1. PROOF STRUCTURING AND ORGANIZATION
================================================================================

Source: Mathematics in Lean (Ch. 2-4), Theorem Proving in Lean 4 (Ch. 5)

INTERMEDIATE STEPS WITH have, let, AND suffices:
-------------------------------------------------
- `have h : P := proof` introduces an opaque fact. The proof value is
  forgotten and cannot be unfolded. PREFERRED for propositions.
- `let x : T := value` introduces a transparent definition that CAN be
  unfolded by simp, dsimp, unfold, and subst. PREFERRED for data.
- `suffices h : P by exact_tactic` says "it suffices to show P" and lets
  you work backwards from the goal.
- Performance tip: Sometimes use `have` even for non-propositions to prevent
  the variable from being unfolded, which can hurt performance.

Pattern matching with have/obtain:
  have <a, b, c> := h        -- destructure products/structures
  obtain <x, hx> := h        -- extract witness from existential
  obtain <h1 | h2> := h      -- split disjunction

The `show` tactic:
  Use `show goal_statement` to clarify what is being proved. It enhances
  readability without affecting proof logic, and can reorder or unfold
  definitions in the goal.

The `set` tactic:
  `set a := complex_expr with h` introduces a local definition AND an
  equality hypothesis h : a = complex_expr, replacing all occurrences
  in the goal. Use `set! a := t with h` to skip automatic replacement.
  Use `set a := t with <- h` for reversed equality h : t = a.

Focusing dots and bullets:
  Use `.` (focusing dot) before tactic blocks to focus on individual
  subgoals. Use `case tag => tactics` for named subgoals.
  Prefer `case` or bullets to organize multi-goal proofs for readability.

================================================================================
2. TACTIC MODE VS TERM MODE
================================================================================

Source: Theorem Proving in Lean 4 (Ch. 3, 5)

WHEN TO USE TERM MODE:
- Short, direct proofs: `exact le_trans h0 h1`
- Simple function application: `exact And.intro hp hq`
- Anonymous constructors: `exact <hp, hq>`
- When the logical structure is straightforward

WHEN TO USE TACTIC MODE:
- Case splitting and induction
- Multi-step proofs requiring intermediate lemmas
- When you need to explore the goal interactively
- Complex rewriting sequences
- Goals requiring multiple automated tactics

MIXING MODES:
- You can embed term-mode proofs inside tactic mode:
    `exact (fun h => h.left)`
- You can use `by` to switch to tactic mode inside a term:
    `(by ring : a * b = b * a)`
- Complex calculations may be clearer as terms; case-splitting
  is often clearer with tactics.

DOT NOTATION:
- Write `h.left` instead of `And.left h`
- Write `h.mp` instead of `Iff.mp h`
- This gives cleaner, more readable proofs

ANONYMOUS CONSTRUCTOR NOTATION:
- Use `<hp, hq>` instead of `And.intro hp hq`
- Use `<proof1, proof2>` for any inductive type when the type is inferrable

================================================================================
3. ESSENTIAL TACTICS REFERENCE
================================================================================

Source: Theorem Proving in Lean 4 (Ch. 5), Mathematics in Lean, Mathlib docs

--- INTRODUCTION TACTICS ---

intro / intros:
  Introduces hypotheses and variables from the goal.
  `intro h` for single; `intros h1 h2 h3` for multiple.
  Use for implications (A -> B) and universal quantifiers (forall x, ...).

rintro:
  Combines intro with pattern matching.
  `rintro <h1, h2>` destructures conjunctions
  `rintro (h1 | h2)` splits disjunctions
  `rintro <x, hx>` extracts existential witness

--- APPLICATION TACTICS ---

exact:
  Provides the exact proof term. Preferred over apply when the solution
  matches exactly. Better error messages than apply if something goes wrong.
  `exact h`
  `exact h.symm`

apply:
  Applies a theorem, generating subgoals for remaining arguments.
  `apply le_trans` creates two subgoals for the intermediate value.
  Works best when partially solving the objective.

refine:
  Like exact but allows holes marked with `?_` that become new goals.
  `refine <h1, ?_>` proves first component, leaves second as goal.

constructor:
  Splits goal into cases for inductive types.
  For And: creates two subgoals (left and right).
  For Iff: creates forward and backward implications.

--- REWRITING TACTICS ---

rw [h]:
  Rewrites using equality h. Left-to-right by default.
  `rw [<- h]` rewrites right-to-left.
  `rw [h1, h2, h3]` chains rewrites sequentially.
  LIMITATION: Cannot rewrite under binders (forall, exists, fun).

simp_rw [h1, h2]:
  Like rw but can rewrite UNDER BINDERS and applies repeatedly.
  Use when rw fails because the target is inside a quantifier or lambda.
  Rules applied in specified order (more control than simp).

--- CASE ANALYSIS ---

rcases h with pattern:
  Pattern-matches on hypothesis h.
  `rcases h with <h1, h2>` for And
  `rcases h with h1 | h2` for Or
  `rcases h with <x, hx>` for Exists
  Nested patterns: `rcases h with <h1, h2, h3> | <h4, h5>`

obtain:
  Like rcases but preferred for extracting existential witnesses.
  `obtain <x, hx> := h`

cases / induction:
  `cases h` performs case analysis on h.
  `induction n with | zero => ... | succ n ih => ...`

by_cases h : P:
  Classical case split on proposition P.
  Creates two goals: one with h : P, one with h : not P.

by_contra h:
  Proof by contradiction. Introduces h : not goal and you prove False.

--- LOGICAL TACTICS ---

left / right:
  Choose which disjunct to prove for Or goals.

use witness:
  Provide witness for existential goal.
  `use 42` or `use 42, proof_of_property`

exfalso:
  Replace current goal with False (ex falso quodlibet).

contradiction:
  Close goal when context contains contradictory hypotheses.

push_neg:
  Push negation inward through quantifiers and connectives.
  Turns `not (forall x, P x)` into `exists x, not (P x)`.

contrapose / contrapose!:
  Transform `P -> Q` into `not Q -> not P`.
  The ! variant additionally applies push_neg.

--- FINISHING TACTICS ---

assumption:
  Close goal if it matches a hypothesis exactly.

trivial:
  Tries assumption, rfl, True.intro, and a few other simple closers.

tauto:
  Proves propositional tautologies. Finishing tactic: closes goal or fails.

decide:
  Proves decidable propositions by computation.

================================================================================
4. AUTOMATION TACTICS (Decision Procedures)
================================================================================

Source: Mathlib tactic documentation, Mathematics in Lean

ring:
  Proves equalities in commutative (semi)rings using only ring axioms.
  Does NOT use local hypotheses. Handles +, *, -, ^, smul.
  Supports variable exponents. Requires commutativity.
  Common pattern: use `rw` to set up, then `ring` to finish.

abel:
  Proves equalities in additive commutative monoids/groups.
  Handles +, -, nsmul/zsmul. Like ring but for additive structures.
  `abel_nf` normalizes without closing the goal.

norm_num:
  Evaluates concrete numerical expressions.
  Proves things like `2 + 3 = 5`, `(0 : R) < 1`, `7 dvd 21`.
  Handles casting between Nat, Int, and rational types.
  Extensible via norm_num plugins.

omega:
  Solves linear arithmetic over Nat and Int using the Omega test.
  Proves goals like `n < m + 1 -> n <= m`.
  Handles natural number subtraction correctly.

linarith:
  Proves goals from linear arithmetic over ordered fields/rings.
  Uses all hypotheses by default.
  `linarith [extra_fact]` adds extra hypotheses.
  `linarith only [h1, h2]` restricts to specific hypotheses.
  Works on dense orders (Q, R) and with limitations on Z, N.

nlinarith:
  Extension of linarith for some nonlinear arithmetic.
  Adds squares-are-nonneg and products of hypothesis pairs.
  `nlinarith [sq_nonneg x, mul_self_nonneg y]`

linear_combination:
  Proves equalities/inequalities by specifying a linear combination
  of hypotheses. More explicit than linarith.
  `linear_combination 2 * h1 + h2 - h3`
  `linear_combination (norm := abel) h1 + h2`  -- custom normalizer

positivity:
  Proves expressions are > 0, >= 0, or != 0.
  Handles arithmetic operations, abs, factorial, gcd, lcm,
  conditionals, min/max, and numeric casts.

field_simp:
  Clears denominators in field expressions. Rewrites to common
  denominator form n/d where neither contains division.
  Common pattern: `field_simp; ring` (clear denominators then prove).
  Auto-proves nonzero denominators when possible.

norm_cast / push_cast / pull_cast:
  Handle coercions between numeric types.
  push_cast pushes casts toward leaves.
  pull_cast pulls casts toward the root.
  norm_cast normalizes casts.

zify / qify:
  `zify` lifts Nat propositions to Int (better subtraction).
  `qify` lifts Int propositions to Rat (better division).
  `zify [hab]` can use extra hypotheses like hab : b <= a.

================================================================================
5. SEARCH AND DISCOVERY TACTICS
================================================================================

Source: Mathlib documentation, Loogle documentation

exact? (formerly library_search):
  Searches the library for a single lemma that closes the goal.
  Shows "Try this: exact ..." suggestion.
  Very useful for finding the right lemma name.

apply?:
  Like exact? but searches for lemmas to apply (leaving subgoals).

rw?:
  Searches for rewriting lemmas that make progress on the goal.

simp?:
  Runs simp and reports which lemmas were used.
  Output can replace the simp call for reproducibility.

Loogle (external tool at loogle.lean-lang.org):
  Search Mathlib by type signature patterns.
  - By constant: `Real.sin` finds all lemmas about sin.
  - By name: `"differ"` finds lemmas with "differ" in name.
  - By pattern: `_ * (_ ^ _)` finds structural matches.
  - By conclusion: `|- _ < _` finds lemmas concluding with <.
  - Combine filters with commas for intersection.
  - Integrates with VSCode: Ctrl-K Ctrl-S.

#check:
  Display the type of a term or theorem.
  `#check @Nat.add_comm` shows full signature with implicits.

#print:
  Print the definition of a term.

#find (deprecated, use Loogle):
  Search for definitions by pattern.

Tab completion:
  In VS Code, use tab completion to explore available lemmas.
  Type a prefix and press Tab to see completions.
  ctrl-click on names to navigate to definitions.

================================================================================
6. CALCULATIONAL PROOFS (calc blocks)
================================================================================

Source: Theorem Proving in Lean 4 (Ch. 4), Mathematics in Lean (Ch. 2)

BASIC PATTERN:
  calc a = b := by proof1
     _ = c := by proof2
     _ = d := by proof3

MIXED RELATIONS:
  calc blocks support mixing =, <, <=, and other relations via
  Trans instances. Example:
  calc a = b := by ...
     _ < c := by ...
     _ <= d := by ...
  Lean infers the final relation (here: a < d).

BEST PRACTICES:
  - Align relation symbols across lines for readability
  - Use `_` as placeholder for the LHS (carried from previous step)
  - Each step requires a justification (by tactic or proof term)
  - calc blocks improve readability over sequential rw chains
  - Keep `:=` alignment optional but recommended for short expressions

COMBINING WITH OTHER TACTICS:
  Use calc inside tactic mode:
    `by calc ...`
  Alternate calc steps with rw/simp/bound for complex chains:
    calc expr
      _ >= simplified := by bound
      _ >= next := by rw [lemma]; bound

================================================================================
7. CONV MODE (Surgical Rewriting)
================================================================================

Source: Theorem Proving in Lean 4 (Conv chapter), Mathlib conv docs

WHEN TO USE:
  1. When rw rewrites at the WRONG location
  2. When you need to rewrite INSIDE function abstractions (under binders)
  3. When you need to target a specific subexpression precisely

NAVIGATION COMMANDS:
  lhs / rhs      -- navigate to left/right side of relation
  intro x        -- enter inside lambda/forall binders
  congr          -- split into subgoals for each argument
  arg i          -- navigate to i-th explicit argument
  arg @i         -- navigate to i-th argument (explicit + implicit)
  enter [...]    -- combined navigation sequence
  ext            -- enter function binders (alternative to intro)
  pattern <expr> -- shortcut: navigate by matching term structure

AVAILABLE TACTICS INSIDE CONV:
  rw [lemma]     -- rewrite at current position
  simp [...]     -- simplify at current position
  ring / norm_num -- close at current position
  change <expr>  -- change to definitionally equal expression
  whnf           -- normalize to weak head normal form
  tactic => ...  -- escape to regular tactic mode

COMMON PATTERNS:

  Pattern 1 - Rewrite under binders:
    conv => lhs; intro x; rw [lemma]

  Pattern 2 - Target specific occurrence:
    conv in b * c => rw [Nat.mul_comm]

  Pattern 3 - Structural navigation:
    conv => lhs; congr; . rw [h1]; . rw [h2]

  Pattern 4 - Occurrence selection:
    conv => arg 1; rw [h]

RULE OF THUMB:
  Use conv when standard rewriting fails. It provides surgical precision
  for navigating deep into term structure.

================================================================================
8. SIMPLIFICATION CONTROL (simp, simp only, simp_rw)
================================================================================

Source: Mathematics in Lean, Mathlib style guide, Community blog

simp:
  Applies all @[simp]-tagged lemmas repeatedly until no more apply.
  Very powerful but can be unpredictable and slow.
  `simp` at the END of a proof (terminal simp) is acceptable.
  NON-terminal simp should be replaced with `simp only [...]`.

simp only [...]:
  Applies ONLY the specified lemmas. More predictable and robust.
  Preferred for non-terminal simplification steps.
  `simp only [h1, h2, mul_comm]`

simp at h:
  Simplify hypothesis h instead of the goal.
  `simp at *` simplifies everything.

simp [...]:
  Add extra lemmas: `simp [mul_comm, h]`
  Use `<-` for reverse: `simp [<- h]`

simp?:
  Runs simp and reports which lemmas were used.
  Replace `simp` with the output for reproducibility.

MATHLIB STYLE RULE:
  "Don't squeeze terminal simp calls unless performance requires it--
  unsqueezed versions remain more readable and avoid excessive lemma
  references that break during renamings."

COMMON simp ATTRIBUTES:
  @[simp]      -- register as default simp lemma
  @[simp, norm_cast] -- for cast-related lemmas
  @[simps]     -- auto-generate simp lemmas for structure projections
  local attribute [simp] h  -- temporary simp lemma in this scope

DANGEROUS PATTERNS TO AVOID:
  - Non-terminal `simp` (breaks when library changes)
  - `erw` after `simp` (indicates missing API)
  - `rfl` after `simp` (also indicates missing API)

dsimp:
  Definitional simplification only. Faster and more predictable.
  Only applies lemmas that hold definitionally (by rfl).

================================================================================
9. TYPE CLASS AND INSTANCE MANAGEMENT
================================================================================

Source: Theorem Proving in Lean 4 (Ch. 10), Mathlib style guide

HOW TYPE CLASSES WORK:
  Type classes enable ad-hoc polymorphism. Mark parameters with
  square brackets [ClassName] and Lean searches its instance database.
  The mechanism uses Prolog-like search, chaining instances recursively.

DEFINING INSTANCES:
  instance : Add Nat where add := Nat.add
  instance [Inhabited a] [Inhabited b] : Inhabited (a x b) where
    default := (default, default)
  Prefer `where` syntax over := { ... }.

SCOPE MANAGEMENT:
  - `local instance` -- restrict to current section
  - `scoped instance` -- active only in namespace or with open scoped
  - `open scoped Namespace` -- activate scoped instances without
    opening the full namespace

OUTPUT PARAMETERS:
  Mark with `outParam` when types should be inferred.
  class HMul (a : Type) (b : Type) (g : outParam Type) where

COMMON PITFALLS:
  - "typeclass instance problem is stuck" -- add type annotations
  - Priority conflicts with default instances -- set priorities explicitly
  - Circular instance dependencies -- causes infinite loops
  - Unexpected instance activation -- use local/scoped

INFERENCE TRIGGERING:
  `inferInstance` explicitly triggers type class resolution.
  `inferInstanceAs (T)` resolves for a specific type.

================================================================================
10. COERCIONS AND TYPE CASTING
================================================================================

Source: Mathlib tactic docs

COMMON COERCION TACTICS:

push_cast:
  Push coercions toward the leaves of the expression tree.
  `push_cast` or `push_cast [lemma1, lemma2]`

pull_cast:
  Pull coercions toward the root of the expression tree.

norm_cast:
  Normalize coercions to a canonical form.
  `norm_cast` or `norm_cast at h`

zify:
  Lift Nat propositions to Int. "Int has well-behaved subtraction."
  `zify [hab]` where hab : b <= a helps handle Nat subtraction.

qify:
  Lift Int propositions to Rat for better division handling.

lift:
  Coerce from supertype to subtype when condition is satisfied.
  `lift n to Nat using hn` transforms n : Int with hn : n >= 0.
  `lift n to Nat with k hk` names the new variable.

BEST PRACTICE:
  - Use zify early when Nat subtraction causes problems
  - Follow field_simp with ring when working in fields
  - Use push_cast to normalize before applying ring/linarith

================================================================================
11. WORKING WITH LOGIC (Quantifiers, Connectives)
================================================================================

Source: Mathematics in Lean (Ch. 3), Theorem Proving in Lean 4

CONJUNCTION (AND):
  Prove: `constructor` or `exact <h1, h2>`
  Unpack: `rcases h with <h1, h2>` or `h.left` / `h.right` or `.1` / `.2`

DISJUNCTION (OR):
  Prove: `left` or `right`
  Unpack: `rcases h with h1 | h2`

IMPLICATION:
  Prove: `intro h` then prove conclusion
  Apply: `exact h1 h2` or `apply h`

BICONDITIONAL (IFF):
  Prove: `constructor` or `exact <forward, backward>`
  Use: `h.mp` (forward), `h.mpr` (backward)
  Rewrite: `rw [h]` applies iff as rewrite

NEGATION:
  not P is defined as P -> False.
  Prove: `intro h` then derive False.
  `push_neg` pushes negation inward.
  `by_contra h` assumes the negation.

EXISTENTIAL:
  Prove: `use witness` or `exact <witness, proof>`
  Unpack: `obtain <x, hx> := h` or `rcases h with <x, hx>`
  Extract function: `choose f hf using h` (Skolemization)

UNIVERSAL:
  Prove: `intro x` then prove P x.
  Apply: `exact h a` or `specialize h a`.
  Hidden quantifiers: Lean unfolds definitions to expose them.

BOUNDED QUANTIFIERS:
  `forall x in s, P x` abbreviates `forall x, x in s -> P x`
  `exists x in s, P x` abbreviates `exists x, x in s /\ P x`

PROOF STRATEGIES:
  - Combine tactics with `<;>` to apply to all goals
  - Use underscores in proof terms to see what Lean expects
  - `ext` proves function equality by pointwise equality
  - `funext` proves function extensionality

================================================================================
12. WORKING WITH SETS AND FUNCTIONS
================================================================================

Source: Mathematics in Lean (Ch. 4)

SET MEMBERSHIP:
  Lean automatically expands set definitions when needed.
  Theorems about membership often include `mem` in their name.

EXTENSIONALITY:
  `ext` proves set equality by showing element-wise membership.
  More efficient than proving mutual subset inclusions.

IMAGE VS PREIMAGE:
  Preimage is often easier: `y in f ^-1' t` unfolds to `f y in t`.
  Image requires decomposing an existential quantifier.

PATTERN MATCHING FOR SETS:
  `rintro (h1 | h2)` decomposes unions.
  Sometimes parentheses around `h1 | h2` are required.

INDEXED OPERATIONS:
  Use `ext` followed by `simp` with membership lemmas to unpack
  indexed unions and intersections into logical propositions.

================================================================================
13. NUMBER THEORY PATTERNS
================================================================================

Source: Mathematics in Lean (Ch. 5)

DIVISIBILITY:
  Clear denominators rather than reasoning with division.
  Avoid Nat subtraction when possible.

PRIMES:
  `Nat.prime_def_lt` for characterization.
  `Nat.Prime.dvd_mul` for the fundamental property.
  `Nat.Prime.eq_one_or_self_of_dvd` for divisor characterization.

MODULAR ARITHMETIC:
  Express as `n % m = k`.
  Use `Nat.add_mul_mod_self_left` and `interval_cases` for
  exhaustive checking over small ranges.

INDUCTION:
  `Nat.strong_induction_on` for strong induction.
  `Finset.induction_on` for finite set induction.
  Mirror recursive definitions with pattern matching syntax.

FACTORIZATION:
  `Nat.factorization n p` for prime multiplicity.
  `factorization_mul'`, `factorization_pow'` for composition.

COMMON APPROACH:
  Contradiction: assume negation, derive p | 1, use norm_num.
  `two_le` for showing n >= 2 from n != 0 and n != 1.

================================================================================
14. ALGEBRAIC PROOF TACTICS
================================================================================

Source: Mathlib tactic documentation

ring:
  Commutative (semi)ring equations. Does NOT use hypotheses.
  Handles: constants, variables, +, *, -, ^, scalar mult.
  Variable exponents supported. Requires commutativity.

abel:
  Additive commutative monoid/group equations.
  Handles: +, -, nsmul, zsmul.

group:
  Multiplicative group equations.

linear_combination:
  Specify exact linear combination of hypotheses.
  `linear_combination h1 + 2 * h2 - h3`
  `linear_combination (norm := ring) ...` custom normalizer.
  `linear_combination (exp := 2) ...` raise to power first.

@[simps]:
  Automatically generates simp lemmas for structure projections.
  `@[simps] def foo : N x Z := (1, 2)` generates foo_fst, foo_snd.
  Recursively generates for nested structures.
  Use `@[simps?]` for verbose output.

@[ext]:
  Register extensionality lemma. ext tactic tries these.
  Prefer partially-applied ext lemmas for cascading simplification.

================================================================================
15. INEQUALITY AND ORDER PROOFS
================================================================================

Source: Mathlib tactic documentation

linarith:
  Linear arithmetic over ordered fields/rings.
  `linarith` uses all context. `linarith [extra]` adds facts.
  `linarith only [h1, h2]` restricts.
  `linarith!` uses stronger reducibility.

nlinarith:
  Nonlinear extension. Adds squares-nonneg and hypothesis products.

positivity:
  Proves > 0, >= 0, or != 0.
  Compositional: handles nested expressions automatically.

gcongr:
  Generalized congruence for inequalities.
  Reduces `x^2 * a + c <= x^2 * b + d` to `a <= b` and `c <= d`.
  `gcongr with i hi` names introduced variables.
  `gcongr x^2 * ?_ + 5` controls depth.
  Auto-discharges side conditions via positivity.

bound:
  Proves inequalities by structural recursion.
  `bound [h0, h1 n]` passes additional hypotheses.
  Good for min/max, powers, and converting between inequality forms.

interval_cases:
  Exhaustive case analysis on bounded integer variables.
  `interval_cases n` when bounds are in hypotheses.
  Auto-detects bounds; for Nat, uses implicit 0 <= n.

monotone / mono:
  Proves monotonicity of expressions built from monotone pieces.

================================================================================
16. ANALYSIS AND TOPOLOGY PATTERNS
================================================================================

Source: Mathlib tactic documentation, Mathematics in Lean

fun_prop:
  Automatically proves function properties:
  - Continuous f, Differentiable R f, Measurable f
  - ContDiff, ContinuousAt/On/Within
  Decomposes functions into elementary components.
  `fun_prop (disch := assumption)` for side conditions.
  Usually MORE POWERFUL than `continuity`.
  Debug: `set_option trace.Meta.Tactic.fun_prop true`
  Common failure: missing theorems for functions (import issues).

continuity:
  Proves Continuous f using @[continuity]-tagged lemmas.
  Deterministic: commits to first matching lemma.
  `fun_prop` is usually preferred.

measurability:
  Proves Measurable f, AEMeasurable f, MeasurableSet s, etc.
  Uses aesop and integrates with fun_prop internally.
  Tag function-level lemmas with @[fun_prop] not @[measurability].

FILTERS:
  Core abstraction for limits and eventual behavior.
  Key: filter order is REVERSED: f <= g iff g.sets subset f.sets.
  `eventually x in f, P x` means P holds for large enough x.
  `Filter.NeBot` is crucial: most theorems require it.
  Use Filter.mem_sup, Filter.inter_mem_iff for membership proofs.

================================================================================
17. STRUCTURING LEAN FILES
================================================================================

Source: Mathlib style guide

FILE HEADER:
  /-
  Copyright (c) YEAR Name. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Name1, Name2
  -/

IMPORTS:
  - All imports immediately follow header, no blank lines
  - Imports are transitive (importing A which imports B gives you both)
  - Lean automatically loads Init library

MODULE DOCSTRING:
  /-! # Title
  Summary of file contents.
  ## Main definitions
  - `Foo` : description
  ## Main theorems
  - `bar` : description
  ## Notation
  - `notation` : description
  -/

DECLARATION ORDER:
  All top-level declarations flush-left.
  No indentation of namespace contents.
  Specify all argument types explicitly.
  Provide return types.

SECTIONS AND VARIABLES:
  Sections automatically insert variables where needed.
  Variables only appear in declarations that reference them.
  Use `section ... end` to scope variables and local attributes.

NAMESPACES:
  Use hierarchical names: Foo.Bar.baz
  `protected def` prevents shorter aliases when opening.
  `_root_` accesses top-level names when inside a namespace.
  `open scoped Namespace` activates scoped instances only.

================================================================================
18. NAMING CONVENTIONS
================================================================================

Source: Mathlib naming conventions guide

CAPITALIZATION:
  - Proofs/theorems: snake_case
  - Props and Types: UpperCamelCase
  - Functions: named like return values
  - Other Type terms: lowerCamelCase
  - Acronyms: upper/lowercase as group based on first char

THEOREM NAMING (conclusion-first):
  Names describe what the theorem proves.
  - `mul_zero` for a * 0 = 0
  - `lt_of_le_of_ne` (hypotheses separated by "of")
  - Use pos, neg, nonpos, nonneg abbreviations
  - Add left/right for structural variants

SYMBOL DICTIONARY:
  or, and, imp/of, iff, not, exists, forall
  mem, union, inter, iUnion, sdiff, compl
  add, sub/neg, mul, pow, div, smul, dvd
  lt, le (or gt, ge when args swap), sup, inf

NAMESPACING:
  Dot notation for intro/elim rules, projections.
  And.intro, Eq.symm, etc.

PREDICATES:
  Prefix by default: isClosed_Icc
  Suffix exceptions: _inj, _injective, _surjective, _bijective,
    _mono, _antitone, _strictMono

PROP-VALUED CLASSES:
  Nouns begin with Is (IsTopologicalRing)
  Adjectives: no Is needed (Normal)

FILE NAMES: UpperCamelCase

SPELLING: American English only

================================================================================
19. STYLE GUIDELINES
================================================================================

Source: Mathlib style guide

LINE LENGTH: Maximum 100 characters per line.

FORMATTING:
  - Spaces around :, :=, and infix operators
  - Operators BEFORE line breaks, not at line starts
  - Indent proof lines by 2 spaces after theorem statements
  - Multi-line theorem statements: indent subsequent lines by 4 spaces
  - `by` keyword at END of preceding line, never alone on a line

TACTIC MODE:
  - All tactic block contents indented
  - Focusing dot `.` not indented
  - Named subgoals use `case` for readability
  - Single tactic per line preferred
  - Short sequences may use semicolons

BINDERS:
  - Prefer `fun` over `lambda`
  - Use `|->` (mapsto arrow) in Mathlib, not `=>`
  - Simple anonymous functions: `(. ^ 2)` with centered dot
  - Space after all binders with explicit types

INSTANCE DEFINITIONS:
  Use `where` syntax:
    instance instOrderBot : OrderBot Nat where
      bot := 0
      bot_le := Nat.zero_le

DEPRECATION:
  @[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name
  Allow 6-month window before deletion.

AVOID:
  - Empty lines within declaration bodies (linter enforced)
  - nonrec when conflicting with namespaced declarations
  - erw or rfl after simp/rw (indicates missing API)

================================================================================
20. DEBUGGING AND ERROR MESSAGES
================================================================================

Source: Theorem Proving in Lean 4 (Interacting chapter), community wisdom

USING THE INFOVIEW:
  - VS Code shows current goal when cursor is in a tactic block
  - Press Ctrl+Shift+Enter to open the Lean infoview panel
  - Place cursor BETWEEN tactics to see intermediate states
  - Incomplete proofs show remaining goals as errors

COMMON ERROR MESSAGES AND FIXES:

  "type mismatch":
    The term you provided doesn't match the expected type.
    Check: argument order, implicit arguments, universe levels.

  "unknown identifier":
    The name isn't in scope. Check imports, namespace openings,
    and spelling (including case sensitivity).

  "typeclass instance problem is stuck":
    Lean can't infer a type class instance. Fix: add type annotations
    or explicit instance arguments.

  "tactic failed, there are unsolved goals":
    Your proof is incomplete. Check the infoview for remaining goals.

  "function expected at ... term has type Prop":
    You're trying to apply a proposition as a function.
    Usually means you need to use .mp, .mpr, or destruct it.

  "invalid 'rewrite', did not find instance of the pattern":
    The pattern for rw doesn't match. Check for implicit arguments
    or use conv mode to target the right location.

DEBUGGING STRATEGIES:
  1. Use `sorry` to stub out parts and focus on one goal at a time.
  2. Use `#check @theorem_name` to see full types with implicits.
  3. Use `show` to clarify what you're proving.
  4. Use `change` to convert to a definitionally equal but clearer form.
  5. Use `trace_state` or just place cursor to see current state.
  6. Use `set_option pp.all true` to see fully explicit terms.
  7. Use `set_option maxHeartbeats 400000` if timeout occurs.
  8. Use `#guard_msgs` to verify expected error messages.

FINDING LEMMAS:
  - Tab completion with ctrl-tab
  - ctrl-click to navigate to definitions
  - exact? / apply? / rw? for automated search
  - Loogle for type-signature-based search
  - Lean Zulip chat for community help

OPTIONS AND CONFIGURATION:
  Options are ALWAYS local (don't persist across files).
  `set_option pp.notation false` to see without notation.
  `set_option pp.universes true` to see universe levels.
  `set_option pp.all true` to see everything explicit.

ATTRIBUTES:
  `@[simp]` / `local attribute [simp]` for simp lemmas
  `attribute [local simp] h` restricts scope to section/file
  Global attributes persist across imports.

================================================================================
21. COMMON BEGINNER MISTAKES
================================================================================

Source: Community wisdom, tutorials, Lean Zulip discussions

1. USING NON-TERMINAL simp:
   simp in the middle of a proof is fragile. It breaks when the
   library changes. Use `simp only [...]` or `simp [...]` with
   explicit lemma lists for non-terminal positions.

2. FORGETTING THAT Nat SUBTRACTION TRUNCATES:
   In Lean, 3 - 5 = 0 for Nat. Use `zify` to lift to Int when
   subtraction is involved, or restructure to avoid subtraction.

3. FIGHTING THE ELABORATOR WITH IMPLICIT ARGUMENTS:
   If Lean can't infer an implicit argument, provide it with @.
   Example: `@Nat.add_comm 3 5` instead of relying on inference.

4. NOT USING THE INFOVIEW:
   The infoview is your primary tool. Always check the goal state
   between tactic applications.

5. TRYING TO USE rw UNDER BINDERS:
   `rw` cannot rewrite inside forall, exists, or fun. Use `simp_rw`
   or `conv` mode instead.

6. OVERUSING ring WHEN HYPOTHESES ARE NEEDED:
   `ring` proves equalities from ring axioms ONLY. It ignores
   hypotheses. If you need hypotheses, use `linear_combination`
   or combine `rw` with `ring`.

7. CONFUSING have AND let:
   `have` forgets the proof (opaque). `let` keeps it (transparent).
   Use `have` for propositions, `let` for data you may need to unfold.

8. NOT USING choose FOR SKOLEMIZATION:
   When you have `h : forall a, exists b, P a b` and need a function,
   use `choose f hf using h` instead of manual extraction.

9. EXPECTING linarith TO HANDLE NONLINEAR GOALS:
   linarith is LINEAR only. For nonlinear, use `nlinarith` with
   extra hints like `nlinarith [sq_nonneg x]`.

10. NOT EXPLORING THE LIBRARY:
    Mathlib is vast. Before writing a long proof, search with
    exact?, apply?, Loogle, or just grep the library.
    Many "obvious" facts are already proved.

11. IGNORING DEFINITIONAL EQUALITY:
    Many things are true by `rfl` due to definitional unfolding.
    Try `rfl` before more complex tactics.

12. FORGETTING UNIVERSE ISSUES:
    Functions must be universe-polymorphic when working across types.
    Universe variables: u, v, w. Check with `set_option pp.universes true`.

================================================================================
22. ADVANCED TECHNIQUES
================================================================================

Source: Mathlib documentation, community blog, advanced tutorials

SIMPROCS (Custom Simplification Procedures):
  Write custom simp procedures for specialized normalization.
  Syntax: `simproc_decl mySimproc (pattern) := fun e => do ...`
  Three approaches: lemma-only, definitional (dsimproc), propositional.
  Best for small steps within larger algorithms.

ATTRIBUTES FOR AUTOMATION:
  @[simp]         -- default simplification lemma
  @[ext]          -- extensionality lemma
  @[continuity]   -- for continuity tactic
  @[measurability]-- for measurability tactic
  @[fun_prop]     -- for fun_prop tactic (PREFERRED for functions)
  @[bound]        -- for bound tactic
  @[gcongr]       -- for gcongr tactic
  @[norm_num]     -- for norm_num extensions
  @[simps]        -- auto-generate simp lemmas for projections
  @[deprecated]   -- mark as deprecated with date

WELL-FOUNDED RECURSION:
  For non-structural recursion, define a well-founded relation.
  Use `termination_by` and `decreasing_by` clauses.
  Lean's equation compiler verifies structural recursion automatically.

AXIOMS IN LEAN 4:
  - propext: logically equivalent Props are equal
  - funext: functions agreeing on all inputs are equal (from Quot)
  - Quot/Quot.sound: quotient types
  - Classical.em: law of excluded middle (safe for reasoning)
  - Classical.choice: data from existence (requires noncomputable)
  Mark choice-dependent definitions as `noncomputable`.

STRUCTURE INHERITANCE:
  `extends Parent1, Parent2` for multiple inheritance.
  Use `{ parent_instance with new_fields := values }` for construction.
  Dot notation routes `instance.method` to `Structure.method instance`.

CUSTOM NOTATION:
  Define notation with priorities for clean mathematical syntax.
  Use `scoped notation` to restrict to namespace.

================================================================================
23. TOOL AND LIBRARY NAVIGATION
================================================================================

Source: Lean community learning resources

KEY REFERENCES:
  - Mathematics in Lean: interactive tactic-based tutorial
  - Theorem Proving in Lean 4: type theory foundations
  - Mathlib API docs: comprehensive reference
  - Loogle (loogle.lean-lang.org): search by type signature
  - Natural Number Game: beginner interactive tutorial

LIBRARY OVERVIEW (Mathlib covers):
  General algebra, category theory, number theory, linear algebra,
  topology via filters, metric spaces, normed spaces, Banach/Hilbert
  spaces, differentiability, measure theory, integration,
  affine/Euclidean geometry, differential manifolds, combinatorics,
  graph theory, probability theory.

  83 of Wiedijk's "100 Famous Theorems" are formalized.

FORMALIZED UNDERGRADUATE MATH:
  Linear algebra (bases, eigenvalues, Jordan decomposition)
  Group theory (Sylow, representations)
  Ring theory (UFDs, Euclidean rings, field theory)
  Real analysis (Taylor's theorem, integration)
  Complex analysis (Cauchy formulas, maximum principle)
  Topology (compactness, connectedness, Banach fixed-point)
  Measure theory (Lebesgue, Fubini, Fourier analysis)
  Probability (strong law of large numbers)

COMMUNITY RESOURCES:
  - Lean Zulip chat: primary community discussion forum
  - Lean community website: guides, blog, documentation
  - GitHub mathlib4: source code and issues
  - "good first issue" labels for new contributors

KEY COMMUNITY ADVICE:
  "Proof assistants are still difficult to use, and you cannot expect
  to become proficient after one afternoon of learning."
  Plan for sustained effort and use the Zulip chat for help.

================================================================================
END OF COMPREHENSIVE LEAN 4 ADVICE COMPILATION
================================================================================
# Comprehensive Lean 4 Proof Techniques, Patterns, and Formalization Methodology
## Compiled from Extensive Web Research (March 2026)

This document supplements the existing `lean_proving_advice_result` file with additional
research focused on proof patterns by mathematical domain, formalization project experience
reports, and advanced tactic usage patterns.

---

# PART 1: EXPANDED TACTIC REFERENCE (NEW FINDINGS)

## 1.1 Logical Symbol Quick Reference (from madvorak/lean4-tactics)

Source: https://github.com/madvorak/lean4-tactics

| Symbol | When in Goal | When in Hypothesis |
|--------|-------------|-------------------|
| `exists` | `use expr` | `obtain <a, b> := expr` |
| `forall` | `intro name` | `apply expr` or `specialize name expr` |
| `not` | `intro name` | `apply expr` or `specialize name expr` |
| `implies` | `intro name` | `apply expr` or `specialize name expr` |
| `iff` | `constructor` | `rw [expr]` or `rw [<-expr]` |
| `and` | `constructor` | `obtain <a, b> := expr` |
| `or` | `left` or `right` | `cases expr with \| inl h => ... \| inr h => ...` |

General-purpose tactics listed:
- `exact expr` -- directly satisfies goal
- `refine expr` -- like exact but permits `?_` placeholders
- `convert expr` -- prove goal by transforming to existing fact
- `convert_to proposition` -- alter goal to new target
- `rw [expr]` -- substitute (use `<-` for reverse)
- `unfold name` -- expand definitions
- `have new_name : proposition` -- assert intermediate result
- `calc` -- chain propositions via transitivity
- `by_cases new_name : proposition` -- split on truth value
- `by_contra new_name` -- assume negation for contradiction
- `exfalso` -- replace goal with False
- `push_neg` -- distribute negation inward
- Automation: `simp`, `simp?`, `simp_all`, `linarith`, `ring`, `exact?`, `apply?`, `rw?`, `aesop`

## 1.2 Constructor Variants (from Mathlib)

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Constructor.html

- **`constructor`** -- apply first matching constructor (may reorder goals)
- **`fconstructor`** -- like constructor but preserves argument order exactly
- **`econstructor`** -- like constructor but only creates goals for non-dependent arguments

## 1.3 Contrapose Tactic Details

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Contrapose.html

- `contrapose` -- transforms `P -> Q` to `not Q -> not P`, or `P <-> Q` to `not P <-> not Q`
- `contrapose!` -- contrapose then push_neg to simplify negated expressions
- `contrapose h` -- reverts h, applies contraposition, reintroduces
- `contrapose h with new_h` -- allows renaming
- `contrapose! +distrib` -- rewrites `not (p and q)` as `not p or not q`

## 1.4 The choose Tactic (Skolemization)

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Choose.html

- Converts `h : forall a, exists b, p a b` into `f : alpha -> beta` and `hf : forall a, p a (f a)`
- `choose!` removes dependencies on propositional arguments when result type is nonempty
- Supports type annotations and pattern matching
- Works with both `exists` and `and` constructs

## 1.5 The set Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Set.html

- `set a := t with h` -- introduces `a := t`, adds `h : a = t`, replaces all occurrences of t with a
- `set a := t with <- h` -- gives `h : t = a` (reversed)
- `set! a := t with h` -- introduces without automatic replacement

## 1.6 The split_ifs Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/SplitIfs.html

- Decomposes goals containing if-then-else into separate branches
- For `g (if p then x else y)`: creates goal with `h : p, g x` and goal with `h : not p, g y`
- Processes nested conditionals starting from topmost non-nested condition
- `split_ifs at *` extends to all hypotheses and goal
- `split_ifs with h1 h2 h3` provides custom names

## 1.7 The have / let / suffices Tactics

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Have.html

- **`have h : t := e`** -- opaque (value forgotten, cannot unfold)
- **`let x : t := e`** -- transparent (can unfold with simp, dsimp, unfold, subst)
- **`suffices h : t' from e`** -- replaces main goal with `t'` where `e` proves `t` given `h : t'`
- Pattern matching supported: `have <h1, h2> := e`
- `clear_value` converts a `let` into a `have`

## 1.8 The abel Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Abel.html

- Solves equations in additive commutative monoids and groups
- Works as both tactic and conversion tactic
- Variants:
  - `abel1` -- fails if target isn't provable by comm monoid/group axioms
  - `abel_nf` -- rewrites to normal form with configuration options
  - `abel!`, `abel1!`, `abel_nf!` -- use more aggressive reducibility
- Examples:
  ```lean
  example [AddCommMonoid a] (a b : a) : a + (b + a) = a + a + b := by abel
  example [AddCommGroup a] (a : a) : (3 : Z) * a = a + (2 : Z) * a := by abel
  ```

## 1.9 The field_simp Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FieldSimp.html

- Normalizes expressions in (semi-)fields by rewriting to common denominator
- Reduces to form `n / d` where neither contains division
- Cross-multiplies field (in)equalities
- Common pattern: `field_simp; ring`
- `field_simp at l1 l2 ...` -- apply at specific locations
- `field_simp (disch := tac)` -- custom discharger for nonzeroness proofs
- `field_simp [t1, ..., tn]` -- extra terms for denominator discharge

## 1.10 The interval_cases Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/IntervalCases.html

- Automates case analysis on variables constrained to finite intervals
- Steps: (1) scan hypotheses for bounds, (2) auto-includes `0 <= n` for naturals, (3) calls fin_cases
- Works with Nat and Int
- `interval_cases n` -- automatic bound detection
- `interval_cases using hl, hu` -- explicit bounds
- `interval_cases h : n` -- named hypothesis

## 1.11 The fin_cases Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FinCases.html

- Exhaustive case analysis on finite types
- Works with `Fintype A`, `Finset`, `Multiset`, `List` membership hypotheses
- Example:
  ```lean
  example (f : Nat -> Prop) (p : Fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val := by
    fin_cases p; simp; all_goals assumption
  ```

## 1.12 The linear_combination Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html

- Proves (in)equality goals as linear combinations of hypotheses
- `linear_combination e` where e uses +, -, *, / on hypothesis proofs
- Default normalizer: `ring1` for equalities
- Custom: `(norm := tac)` allows `abel`, `field_simp`, `skip`
- Power variant: `(exp := n)` raises goal to nth power first
- Example:
  ```lean
  example {a b : Q} (h1 : a = 1) (h2 : b = 3) : (a + b) / 2 = 2 := by
    linear_combination (h1 + h2) / 2
  ```

## 1.13 The gcongr Tactic (Generalized Congruence)

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr/Core.html

- Reduces relational goals between expressions with same structure into simpler subgoals
- Pattern matching: identifies when LHS and RHS follow same function application pattern
- Applies `@[gcongr]`-tagged lemmas
- Recursive descent on "main" goals, auto-discharges "side" goals via positivity
- Example:
  ```lean
  example {a b x c d : R} (h1 : a + 1 <= b + 1) (h2 : c + 2 <= d + 2) :
      x ^ 2 * a + c <= x ^ 2 * b + d := by
    gcongr
    . linarith
    . linarith
  ```
- `gcongr x ^ 2 * ?_ + 5` -- control pattern/depth
- `gcongr with i hi` -- name bound variables

## 1.14 The bound Tactic

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Bound.html

- Aesop wrapper for proving inequalities through recursive structural decomposition
- Transitions between `0 <= x` and `x <= y` formats automatically
- Special handling for `1 <= x`, `1 < x`, `x <= 1`, `x < 1`
- Rule categories:
  - Apply rules (`@[bound]`): scored by hypothesis complexity
  - Forward rules (`@[bound_forward]`): expose hidden inequalities
  - Guessing rules: handle min/max ambiguity
- Closes numerical goals with `norm_num`, others with `linarith`
- `bound [h0, h1 n, ...]` -- pass additional hypotheses

## 1.15 The zify / qify Tactics

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Zify.html,
       https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Qify.html

- **zify**: lifts Nat propositions to Int ("Int has well-behaved subtraction")
  - `zify` -- convert goal
  - `zify at h` -- convert hypothesis
  - `zify [hab]` -- provide extra lemmas for simplification
  - Dual to `lift` tactic (lift goes supertype -> subtype)
- **qify**: lifts Nat/Int propositions to Rat ("Rat has well-behaved division")
  - Same syntax patterns as zify

## 1.16 The ext Tactic (Extensionality)

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ext.html

- Proves equality by showing objects behave identically
- Uses `@[ext]`-tagged lemmas with prioritized, composable rules
- Key design principle: partially-applied ext lemmas are preferred
  - `f.comp of = g.comp of -> f = g` is BETTER than `(forall x, f (of x) = g (of x)) -> f = g`
  - This enables chaining of type-specific extensionality rules
- For bundled morphisms, specialized ext lemmas take priority over generic ones

## 1.17 Polyrith Status Update

Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html

- **polyrith is NO LONGER SUPPORTED** -- depended on external Sage server (shut down)
- Alternative: use `grobner` tactic for polynomial reasoning via Grobner basis computation
- `grobner` does not generate `linear_combination` suggestions like polyrith did

---

# PART 2: COMPREHENSIVE THEOREM SEARCH GUIDE

Source: Lean Community Blog - "Searching for Theorems in Mathlib" (2025-06-25)
https://leanprover-community.github.io/blog/posts/searching-for-theorems-in-mathlib/

## 2.1 Search Tools Ranked by Effectiveness

### In-Editor Tactics (fastest feedback loop):
1. **`exact?`** -- searches library for single lemma closing the goal
2. **`apply?`** -- finds lemmas applicable to goal (may leave subgoals)
3. **`rw?`** -- discovers applicable rewrite lemmas
4. **`simp?`** -- runs simp, reports which lemmas used
5. **`hint`** -- tries multiple registered tactics, reports successes
6. **`rw_search`** -- exhaustive rewrite search
7. **`aesop`** -- general automated solver

### Web-Based Tools:
1. **Loogle** (loogle.lean-lang.org) -- type signature search
   - Example: `(?a -> ?b) -> List ?a -> List ?b` finds `List.map`
   - Available in VS Code extension
   - TIP: Add filters incrementally to avoid empty results
2. **Moogle** -- LLM-based semantic search (VS Code extension)
3. **LeanSearch** -- supports augmenting previous queries
4. **LeanExplore** -- allows selecting different Lean libraries

### Community Resources:
1. **Zulip Chat** -- "Is there code for X?" channel
2. **Curated Lists**:
   - Mathlib overview (by mathematical topic)
   - Undergrad list
   - Wiedijk's 100 Theorems (83/100 formalized)
   - 1000+ Theorems project with Wikidata identifiers

### Key Insight from the Blog:
"Learn naming conventions to improve search effectiveness" -- the naming convention system
is the single most powerful technique for finding theorems by name.

---

# PART 3: SIMP INTERNALS AND SIMPROCS

## 3.1 How simp Works

Source: Lean Community Blog - "Simp, made simple" (2025-12-02)

Core loop operates in three stages:
1. **Preprocedures** -- execute on expression BEFORE recursing (outside-in)
2. **Subexpression traversal** -- process child expressions
3. **Postprocedures** -- execute AFTER subexpressions simplified (inside-out)

Step types returned by each simplification:
- **`visit`** -- preprocedures should retry on simplified expression
- **`continue`** -- move to next sibling/parent; prevents re-running same procedure
- **`done`** -- expression is in normal form; stop

Key insight: "Every simp lemma is internally turned into a simproc for simp's consumption."

## 3.2 Simprocs (Custom Simplification Procedures)

Source: Lean Community Blog - "Simprocs for the Working Mathematician" (2025-05-26)

Definition: "A rewriting rule which, given an expression matching its left hand side, computes
a simpler expression and constructs a proof on the fly."

### Advantages over simp lemmas:
- Avoid combinatorial explosion (one simproc replaces infinitely many lemmas)
- Computation capability (generate answers dynamically)
- Performance optimization (selectively simplify before branches)

### Built-in Simproc Examples:
1. **`existsAndEq`** -- simplifies `exists x, P x and x = a` to `P a`
2. **`Nat.reduceDvd`** -- evaluates `a | b` for numerals to True/False
3. **`Finset.Icc_ofNat_ofNat`** -- converts `Finset.Icc a b` to `{1, 2, 3, 4}`
4. **`reduceIte`** -- simplifies `if P then a else b` by evaluating P

### Usage:
```lean
simp only [simproc_name]
```

### Limitation: Simprocs only work with `simp`, not `rw`.

---

# PART 4: FORMALIZATION PROJECTS AND EXPERIENCE REPORTS

## 4.1 PFR (Polynomial Freiman-Ruzsa) Conjecture

Source: https://teorth.github.io/pfr/
Led by: Terence Tao (UCLA) and Yael Dillies (University of Stockholm)

**Result formalized**: If A is nonempty subset of F_2^n with |A+A| <= K|A|, then A can be
covered by at most 2K^12 cosets of a subspace of bounded cardinality.

**Methodology**:
- Used Lean 4's **blueprint methodology**: formal verification + mathematical documentation
- Technical backbone: Shannon entropy theory
- Developed Shannon entropy inequalities as essential infrastructure
- Progressive refinement: exponent reduced 12 -> 11 -> 9 across project phases
- Currently extending to other bounded torsion groups

**Key lesson**: Infrastructure development (Shannon entropy) was crucial prerequisite.

## 4.2 Mathlib Library Scale

Source: https://leanprover-community.github.io/mathlib-overview.html

**Coverage**: Category theory, algebra (groups through Galois theory), number theory,
linear algebra, topology, real/complex analysis, measure theory, geometry, combinatorics.

**Statistics**: 83 of 100 famous theorems formalized.

**Specific highlights**:
- Number Theory: quadratic reciprocity, sum of two/four squares, Pell equations, prime number theorem
- Analysis: Stone-Weierstrass, Banach-Steinhaus, Hahn-Banach, Taylor's theorem, Cauchy integral
- Topology: Baire theorem, Arzela-Ascoli, Urysohn's lemma
- Algebra: Hilbert basis theorem, Galois correspondence, Cayley-Hamilton, Nullstellensatz
- Geometry: schemes, differentiable manifolds, Lie groups
- Combinatorics: Hall's marriage, Ramsey theory, Turan, Roth

## 4.3 Kevin Buzzard / Xena Project Observations

Source: https://xenaproject.wordpress.com/

Key blog post findings:
1. **"Accelerating mathematics"** (Feb 2026): "Lean's mathlib is still missing literally
   hundreds of definitions used in modern day mathematics." Growing ITP libraries requires
   both human expertise and computational resources.

2. **"Formalization of Erdos problems"** (Dec 2025): AI-assisted approaches (Aristotle tool)
   now handle informal-to-formal translation. AI discovered misformalization errors.
   Formalization timelines are accelerating.

3. **"Formal or not formal?"** (Oct 2025): Critical bottleneck identified -- modern research
   mathematics relies on definitions not yet formalized in Lean.

4. **"AI at IMO 2025"** (Aug 2025): Review of formal vs informal AI approaches for
   mathematics competition problems.

## 4.4 Formalizing Class Field Theory

Source: Lean Community Blog (2025-08-22)
CMI HIMR summer school at Oxford, July 2025, focused on formalization methodology.

## 4.5 Sphere Packing Project

Source: Lean Community Blog (2026-03-02)
Evolution of the sphere packing initiative, culminating in autoformalisation efforts.

## 4.6 Fermat's Last Theorem Project

Led by Kevin Buzzard. Ongoing effort to formalize FLT in Lean 4, starting with regular primes.

## 4.7 Key Community Blog Posts (2025-2026)

Source: https://leanprover-community.github.io/blog/

| Date | Title | Key Topic |
|------|-------|-----------|
| 2026-03-02 | Sphere Packing Project Post 1 | Autoformalisation |
| 2026-02-27 | Fantastic Simprocs 3 | Writing custom simprocs |
| 2026-01-13 | Tradeoffs of subobjects | Design patterns for type definitions |
| 2025-12-02 | Simp, made simple | Simp internals |
| 2025-08-22 | Formalizing Class Field Theory | Oxford school report |
| 2025-08-03 | Simons Foundation Workshop | MPS Workshop summary |
| 2025-06-25 | Searching for Theorems | Comprehensive search guide |
| 2025-06-24 | Affine group schemes | Algebraic tori theory |
| 2025-06-17 | Abelian categories | Grothendieck categories, Freyd-Mitchell |
| 2025-05-26 | Simprocs for Working Mathematician | Simproc introduction |

---

# PART 5: PROOF PATTERNS BY MATHEMATICAL DOMAIN

## 5.1 Number Theory

**Available in Mathlib**: quadratic reciprocity, sum of two/four squares, infinitude of primes,
Wilson's lemma, Euler's totient/Fermat's little theorem, Dirichlet unit theorem, Bernoulli
numbers, Hensel's lemma, Matiyasevic's theorem, Pell's equation.

**Common tactic patterns**:
- Divisibility: `norm_num`, `omega`
- Modular arithmetic: `omega`, `norm_num`, `interval_cases`
- Induction on naturals: `induction n with | zero => ... | succ k ih => ...`
- Prime factorization: `Nat.factorization`

## 5.2 Inequality Proofs

**Key tactics** (in order of specificity):
1. `omega` -- linear arithmetic on Nat/Int (most efficient for pure integer goals)
2. `norm_num` -- numerical evaluation
3. `linarith` -- linear arithmetic over ordered fields
4. `nlinarith` -- nonlinear arithmetic (with hints like `sq_nonneg`)
5. `positivity` -- prove nonneg/positivity structurally
6. `gcongr` -- monotonicity/congruence for inequalities
7. `bound` -- recursive structural inequality decomposition
8. `linear_combination` -- explicit combination of hypotheses

**Patterns**:
```
-- Chain with calc
calc a <= b := by linarith
     _ < c := by nlinarith [sq_nonneg x]
     _ <= d := by gcongr; linarith

-- Positivity
example (x : R) : 0 <= x ^ 2 := by positivity

-- Monotonicity
example (a b : R) (h : a <= b) : a + 1 <= b + 1 := by gcongr
```

## 5.3 Set Theory

**Available**: ordinal/cardinal arithmetic, ZFC model, Schroeder-Bernstein, Cantor.

**Common patterns**:
```
-- Set extensionality
ext x; simp [Set.mem_inter_iff, ...]

-- Subset proofs
intro x hx; exact ...

-- Membership
exact <hs, ht>
```

## 5.4 Algebra

**Available**: Lagrange, Sylow, Chinese remainder, Hilbert basis, Galois correspondence,
Cayley-Hamilton, Nullstellensatz, fundamental theorem of algebra.

**Common patterns**:
```
-- Ring equalities
ring

-- Abelian group
abel

-- Field with denominators
field_simp; ring
```

## 5.5 Analysis

**Available**: Stone-Weierstrass, Banach-Steinhaus, Hahn-Banach, Rolle, mean value theorem,
Taylor, Cauchy integral, Liouville, dominated convergence, Fubini.

**Common patterns**:
```
-- Continuity
continuity  -- or fun_prop (preferred)

-- Differentiability
fun_prop

-- Filter-based limits
Filter.Tendsto, nhds, atTop
```

## 5.6 Topology

**Available**: Urysohn's lemma, Baire theorem, Arzela-Ascoli, Heine-Cantor.

## 5.7 Combinatorics

**Available**: Hall's marriage, Ramsey, Turan, Cauchy-Davenport, Roth.

**Finite type patterns**:
```
-- Exhaustive case analysis
fin_cases i <;> simp [*]

-- Finite set operations
Finset.range, Finset.sum, Finset.prod
```

---

# PART 6: MATHLIB STYLE GUIDE HIGHLIGHTS

Source: https://leanprover-community.github.io/contribute/style.html

## Formatting Rules
- Maximum 100 characters per line
- 2-space indentation for proof bodies
- Top-level declarations flush-left
- `by` at end of preceding line, never alone
- One tactic per line (except short sequences)
- Focusing dots (`.`) for subgoals

## Variable Conventions
- `u, v, w` -- universes
- `alpha, beta, gamma` -- generic types
- `x, y, z` -- elements; `h, h1` -- hypotheses
- `m, n, k` -- naturals; `i, j, k` -- integers
- `G` -- groups, `R` -- rings, `K`/`k` -- fields, `E` -- vector spaces

## Key Rules
- Arguments left of colon preferred over implications/quantifiers
- Don't squeeze terminal simp calls (more maintainable unsqueezed)
- Use `fun` (not `lambda`) with `|->` arrow (preferred over `=>`)
- Explicitly state argument types and return types
- American English spelling

## Definition Transparency
- `reducible` (via `abbrev`) -- always unfolded
- `semireducible` (default `def`) -- rarely unfolded
- `irreducible` -- never unfolded unless explicitly requested

---

# PART 7: NAMING CONVENTIONS (COMPLETE)

Source: https://leanprover-community.github.io/contribute/naming.html

## Capitalization
- Propositions/Proofs: `snake_case` (e.g., `map_one`)
- Types/Structures/Classes: `UpperCamelCase` (e.g., `OneHom`)
- Functions: named like return values
- Other terms: `lowerCamelCase` (e.g., `toFun`)
- Acronyms: treated as groups (e.g., `LE` not `Le`)
- Files: `UpperCamelCase.lean`
- Spelling: American English

## Theorem Name Pattern: `conclusion_of_hypothesis`

### Symbol Dictionary:
- **Logic**: `or`, `and`, `imp`/`of`, `iff`, `not`, `exists`, `forall`
- **Sets**: `mem`, `union`, `inter`, `iUnion`, `iInter`, `sdiff`, `compl`
- **Algebra**: `zero`, `add`, `neg`/`sub`, `one`, `mul`, `pow`, `div`, `inv`, `dvd`, `sum`, `prod`
- **Lattices**: `le`/`ge`, `sup`, `inf`, `iSup`, `iInf`, `bot`, `top`
- **Properties**: `refl`, `symm`, `trans`, `antisymm`, `comm`, `assoc`
- **Abbreviations**: `pos`, `neg`, `nonpos`, `nonneg`

### Structural Lemma Names:
- `.ext` / `.ext_iff` -- extensionality
- `f_injective` / `injective_f` -- injectivity; `f_inj` bidirectional
- `.induction_on` -- motive Prop, value first
- `.induction` -- motive Prop, constructions first
- `.recOn` -- motive Sort u, value first
- `.rec` -- motive Sort u, constructions first

### Predicates:
- Prefix by default: `isClosed_Icc`
- Suffix exceptions: `_injective`, `_surjective`, `_bijective`, `_monotone`, `_antitone`, `_strictMono`

### Prop-valued Classes:
- Noun-like: prefix with `Is` (e.g., `IsTopologicalRing`)
- Adjective-like: no prefix (e.g., `Normal`)

---

# PART 8: MATHEMATICS IN LEAN TUTORIAL STRUCTURE

Source: https://leanprover-community.github.io/mathematics_in_lean/
Authors: Jeremy Avigad and Patrick Massot (v4.19.0)

## Complete Chapter List:
1. Introduction
2. **Basics** -- calculating, algebraic proofs, theorem application, structural facts
3. **Logic** -- universal/existential quantifiers, negation, conjunction, disjunction, convergence
4. **Sets and Functions** -- set theory, function properties, Schroeder-Bernstein
5. **Elementary Number Theory** -- irrational roots, induction, primes
6. **Discrete Mathematics** -- Finsets, fintypes, counting, inductively defined types
7. **Structures** -- defining structures, algebraic structures, Gaussian integers
8. **Hierarchies** -- basics, morphisms, sub-objects
9. **Groups and Rings** -- monoid/group theory, ring theory
10. **Linear Algebra** -- vector spaces, linear maps, subspaces, matrices, dimension
11. **Topology** -- filters, metric spaces, topological spaces
12. **Differential Calculus** -- elementary and advanced calculus in normed spaces
13. **Integration and Measure Theory**

---

# PART 9: INDUCTION AND EXISTENTIAL PATTERNS (FROM OFFICIAL TEXTBOOK)

Source: Theorem Proving in Lean 4 (lean-lang.org)

## 9.1 Induction Patterns

### Structural Induction:
- Pattern matching on constructors (`zero`, `succ x`)
- "The equations used to define these functions hold definitionally"
- Recursive calls must operate on structurally smaller subterms

### Course-of-Values Recursion:
- Automatically generated `below` and `brecOn` constants
- Access to ALL predecessors, not just immediate predecessor

### Well-Founded Recursion:
- For non-structural decrease, define custom well-founded relation
- Use `termination_by` and `decreasing_by` clauses

### Pattern Matching Features:
- Wildcards (`_`) for unused values
- Overlapping patterns (first match applies)
- Nested patterns (`(m+1, n+1)`)
- Dependent patterns with type constraints

## 9.2 Universal Quantifier Patterns

- Introduction: `intro x` or function notation `fun x => ...`
- Elimination: `h t` instantiates `h : forall x, p x` at `t`
- `forall x, p x` is notation for dependent function type `(x : alpha) -> p x`
- Implicit arguments in `{x y z}` inferred automatically

## 9.3 Equality and Rewriting

- Reflexivity (`rfl`): proves computational equalities like `2 + 3 = 5`
- Symmetry (`Eq.symm`), Transitivity (`Eq.trans`)
- Substitution (`Eq.subst`, `h triangle e`): given `h1 : a = b` and `h2 : p a`, derive `p b`
- Congruence: `congrArg f h1`, `congrFun h2 a`, `congr h2 h1`
- calc blocks: chain relations via Trans typeclass, supports mixed relations

## 9.4 Existential Patterns

- Introduction: `use witness` or `Exists.intro witness proof`
- Anonymous: `<witness, proof>`
- Elimination: `obtain <x, hx> := h`, `choose f hf using h`

---

# PART 10: SORRY AND INCREMENTAL DEVELOPMENT

Source: Theorem Proving in Lean 4 - Interacting chapter

## Key Commands:
- **`sorry`** -- placeholder for incomplete proofs; emits warning "declaration uses 'sorry'"
- **`#check expr`** -- display type without evaluating
- **`#eval expr`** -- evaluate and display (fails with sorry; use `#eval!` to override)
- **`#guard_msgs`** -- verify expected messages in test suites

## Incremental Strategy:
1. State theorem
2. Use `sorry` for all sub-goals
3. Identify key decomposition (induction, cases, etc.)
4. Fill in sub-goals one at a time
5. Polish: replace verbose proofs with concise alternatives

---

# PART 11: LEAN 4 METAPROGRAMMING FOR CUSTOM TACTICS

Source: Lean 4 Metaprogramming Book
https://leanprover-community.github.io/lean4-metaprogramming-book/

## Book Structure:
1. Introduction -> 2. Overview -> 3. Expressions -> 4. MetaM ->
5. Syntax -> 6. Macros -> 7. Elaboration -> 8. DSLs -> 9. Tactics -> 10. Cheat-sheet

## Two Approaches:

### Macro-Based (lightweight):
```lean
macro "custom_sorry_macro" : tactic => `(tactic| sorry)
```
- Extensible via multiple `macro_rules` blocks
- Good for tactic combinators

### Direct TacticM (full power):
```lean
elab "my_tactic" : tactic => do
  let goal <- getMainGoal
  let target <- getMainTarget
  -- manipulate goal...
```

## Essential APIs:
- `getMainGoal` / `getMainTarget` -- access primary goal
- `withMainContext` -- ensure proper elaboration context (ALWAYS use before accessing goals)
- `getLCtx` -- access local context (hypotheses)
- `isExprDefEq expr1 expr2` -- check definitional equality
- `closeMainGoal` -- close goal with provided term
- `mvarId.assert name type value` -- add hypothesis
- `mvarId.define name type value` -- add let binding
- `throwTacticEx` -- report errors with `m!"..."` format

## Best Practice: Prefer `Lean.Elab.Tactic.*` over `Lean.Meta.Tactic.*` APIs.

---

# PART 12: UNDERGRADUATE MATH FORMALIZATION STATUS

Source: https://leanprover-community.github.io/undergrad_todo.html

## Still Missing from Mathlib:
- **Linear Algebra**: Jordan normal form, Gaussian elimination, diagonalization, endomorphism exponential
- **Group Theory**: Representation theory, character theory, Fourier on finite groups
- **Analysis**: Series convergence tests (some), improper integrals, convexity details
- **Complex Analysis**: Cauchy-Riemann, contour integrals, Laurent series, residue theorem
- **Geometry**: Conic sections, isometries, regular polygons
- **Multivariable**: Differential equations, submanifolds, Lagrange multipliers
- **Probability**: Random variables, convergence theorems
- **Numerical**: Linear systems solving, iterative methods, FFT

## Formalized (100 Theorems Project -- 83/100):
Including: irrationality of sqrt(2), fundamental theorem of algebra, quadratic reciprocity,
Pythagorean theorem, Schroeder-Bernstein, Cantor, Sylow theorems, Cayley-Hamilton,
prime number theorem, Abel-Ruffini, Heron's formula, L'Hopital's rule, Taylor's theorem,
divergence of harmonic series, Minkowski's theorem, Dirichlet's theorem.

---

# PART 13: TACTIC SELECTION HEURISTICS

| Goal Type | Try First | Then Try | Last Resort |
|-----------|-----------|----------|-------------|
| Equality of numbers | `norm_num` | `omega`, `decide` | `native_decide` |
| Ring/field equality | `ring` | `field_simp; ring` | `linear_combination` |
| Linear inequality | `linarith` | `omega` (Nat/Int) | `nlinarith` |
| Nonlinear inequality | `nlinarith [hints]` | `positivity`, `bound` | `gcongr` + manual |
| Set equality | `ext x; simp` | `aesop` | manual |
| Function equality | `ext x; simp` | `funext` | manual |
| Iff goal | `constructor` | `simp`, `tauto` | manual |
| Exists goal | `use witness` | `exact <w, p>` | `choose` + manual |
| Forall goal | `intro x` | -- | -- |
| Disjunction | `left`/`right` | `tauto`, `omega` | `decide` |
| Conjunction | `constructor` | `exact <p1, p2>` | -- |
| Contradiction | `by_contra h` | `exfalso`, `absurd` | `omega`, `linarith` |
| If-then-else | `split_ifs` | `simp [if_pos h]` | -- |
| Decidable prop | `decide` | `native_decide` | -- |
| Finite type | `fin_cases` | `interval_cases` | `omega` |
| Cast issues | `push_cast; ring` | `norm_cast`, `zify` | `qify` |
| Unknown lemma | `exact?` | `apply?`, `rw?` | `simp?`, Loogle |
| Monotonicity | `gcongr` | `mono` | `bound` |
| Continuity | `fun_prop` | `continuity` | manual |
| Measurability | `measurability` | `fun_prop` | manual |
| Abelian group eq | `abel` | `ring` (if commutative ring) | -- |
| Group eq | `group` | -- | manual |

---

# PART 14: KEY RESOURCES DIRECTORY

## Official Documentation
- Theorem Proving in Lean 4: https://lean-lang.org/theorem_proving_in_lean4/
- Mathematics in Lean: https://leanprover-community.github.io/mathematics_in_lean/
- Mathlib4 Docs: https://leanprover-community.github.io/mathlib4_docs/
- Lean 4 Metaprogramming Book: https://leanprover-community.github.io/lean4-metaprogramming-book/

## Community Resources
- Lean Community Blog: https://leanprover-community.github.io/blog/
- Zulip Chat: https://leanprover.zulipchat.com/
- Natural Number Game: https://adam.math.hhu.de/#/g/leanprover-community/NNG4
- Tactics Overview: https://github.com/madvorak/lean4-tactics
- Kevin Buzzard's Course: https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/

## Search Tools
- Moogle (semantic search): available in VS Code extension
- Loogle (type-based search): loogle.lean-lang.org + VS Code extension
- LeanSearch, LeanExplore (NL search)
- Mathlib naming conventions: https://leanprover-community.github.io/contribute/naming.html

## Major Formalization Projects
- PFR Conjecture: https://teorth.github.io/pfr/
- Mathlib Overview: https://leanprover-community.github.io/mathlib-overview.html
- 100 Theorems: https://leanprover-community.github.io/100.html
- Xena Project Blog: https://xenaproject.wordpress.com/
- FLT Project (Buzzard): ongoing

## Style and Contribution
- Style Guide: https://leanprover-community.github.io/contribute/style.html
- Naming Conventions: https://leanprover-community.github.io/contribute/naming.html
- Undergrad TODO: https://leanprover-community.github.io/undergrad_todo.html
