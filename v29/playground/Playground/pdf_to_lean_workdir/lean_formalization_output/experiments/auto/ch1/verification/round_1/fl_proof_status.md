# Chapter 1 — Proof Status Log (Round 1)

## Summary
- Total theorems: 2
- Proved: 1 (Ch1_theorem_5)
- Unprovable due to formalization bug: 1 (Ch1_theorem_11)
- Coverage check: 100% (11/11 statements preserved)

---

## Ch1_theorem_5 (Proposition 1.1: Homomorphisms preserve inverses and identity) — COMPLETED

**Attempt 1 (SUCCESS):** Used `map_one f` for the identity part and `map_inv f g` for the inverse part. Combined with anonymous constructor: `exact ⟨map_one f, fun g => map_inv f g⟩`.

- lake build: success (no errors for ch1, only style warnings about long lines in comment blocks)
- Coverage check: 11/11 statements preserved (100%)
- Helper lemmas added: none
- Final proof strategy: Direct application of Mathlib's `map_one` and `map_inv` lemmas for `MonoidHom`/group homomorphisms.

---

## Ch1_theorem_11 (Theorem 1.1: Cayley's theorem — every group is a concrete group) — BLOCKED BY UNIVERSE BUG

### Root cause:
`Ch1_def_1` has two independent universe parameters:
```
Ch1_def_1.{u_1, u_2} : (G : Type u_1) → [Group G] → Prop
```
The existential `∃ (S : Type u_2)` uses universe `u_2` independent of `G`'s universe `u_1`. The theorem inherits both universe params, requiring a proof for ALL pairs `(u_1, u_2)`. Cayley's embedding uses `S = G : Type u_1`, which doesn't match `Type u_2` when `u_1 ≠ u_2`.

### All attempted approaches:

**Attempt 1:** `exact ⟨G, MulAction.toPermHom G G, ...⟩`
→ Failed: "Application type mismatch: G has type Type u_1 but expected Type u_2"

**Attempt 2:** `unfold Ch1_def_1` then `refine ⟨G, ...⟩`
→ Same universe mismatch after unfolding

**Attempt 3:** `use G, MulAction.toPermHom G G`
→ Same error: "Type mismatch: G has type Type u_1 but expected Type u_2"

**Attempt 4:** `dsimp only [Ch1_def_1]` then exact
→ Same universe mismatch

**Attempt 5:** `simp [Ch1_def_1]` then exact
→ Same error

**Attempt 6:** `change ∃ (S : Type _), ...` then provide G
→ `Type _` creates a fresh universe, same mismatch

**Attempt 7:** `have h : ∃ (S : Type _), ... := ⟨G, ...⟩; exact h`
→ `have` succeeds but `exact h` fails: "h has type ∃ S f, ... but expected Ch1_def_1 G" (different universes)

**Attempt 8:** `have h := ...; convert h`
→ Leaves unsolvable iff goal: `Ch1_def_1 G ↔ ∃ S f, ...` (different universes)

**Attempt 9:** `constructor; constructor; case w => exact G`
→ Same: "G has type Type u_1 but expected Type u_2"

**Attempt 10:** Use `ULift G` as witness
→ `ULift.{u_2} G : Type (max u_1 u_2)` ≠ `Type u_2` in general; also stuck at universe constraint

**Attempt 11:** `@MyDef.{u, u} G _` with explicit same-universe annotation
→ Works! But can't change the theorem statement to use this annotation

**Attempt 12:** Helper lemma with `∃ (S : Type u), ...` (same universe)
→ Helper works, but `exact helper G` fails: type mismatch between helper's ∃ and Ch1_def_1

**Attempt 13:** Term-mode proof `Exists.intro G ⟨...⟩`
→ Same universe mismatch at `Exists.intro G`

### Conclusion:
This theorem is **unprovable as formalized** due to the independent universe parameter in `Ch1_def_1`. The definition should use a single universe for both `G` and `S`. Reported in `fl_statements_unfaithful_arguments.md`.

- lake build: compiles with `sorry` warning
- Coverage check: 11/11 statements preserved (100%)
- Helper lemmas added: none
- Proof strategy notes: The mathematical proof (Cayley's theorem via left regular representation) is straightforward — `MulAction.toPermHom G G` gives the embedding and faithfulness of the action gives injectivity. The blocker is purely a universe-level issue in the formalization.
