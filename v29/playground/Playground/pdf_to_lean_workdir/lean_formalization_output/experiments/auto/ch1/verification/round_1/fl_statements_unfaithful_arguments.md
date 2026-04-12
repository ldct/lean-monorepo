# Unfaithful/Unprovable Formalization Arguments — Chapter 1

## Ch1_def_1 (Definition 1.1, Concrete group) — UNIVERSE BUG

### LaTeX quote:
```latex
\begin{definition}[Definition 1.1, Concrete group]
A set $G$ is a group iff it is the set of symmetries of something.
\end{definition}
```

### Current Lean statement:
```lean
def Ch1_def_1 (G : Type*) [Group G] : Prop :=
  ∃ (S : Type*), ∃ (f : G →* Equiv.Perm S), Function.Injective f
```

### Issue:
The definition uses `Type*` twice — once for `G` and once for `S` in the existential. In Lean 4, each `Type*` creates a fresh auto-bound universe variable, resulting in:

```
Ch1_def_1.{u_1, u_2} : (G : Type u_1) → [Group G] → Prop
```

where `u_1` is the universe of `G` and `u_2` is the universe of `S`. These are **independent** universe parameters.

### Why this makes Ch1_theorem_11 unprovable:

The theorem `Ch1_theorem_11 (G : Type*) [Group G] : Ch1_def_1 G` inherits both universe parameters:
```
Ch1_theorem_11.{u_1, u_2} : (G : Type u_1) → [Group G] → Ch1_def_1.{u_1, u_2} G
```

This requires proving `∃ (S : Type u_2), ∃ (f : G →* Equiv.Perm S), Function.Injective f` for **arbitrary** `u_2`. Cayley's theorem naturally uses `S = G`, but `G : Type u_1` ≠ `Type u_2` when `u_1 ≠ u_2`. There is no general way to embed a type from one universe into another.

### Proposed fix:
Change the second `Type*` to share the universe with `G`. Either:

**Option A** — Use explicit universe variable:
```lean
universe u
def Ch1_def_1 (G : Type u) [Group G] : Prop :=
  ∃ (S : Type u), ∃ (f : G →* Equiv.Perm S), Function.Injective f
```

**Option B** — Keep `Type*` for `G` but use `Type _` for `S`:  
Unfortunately `Type _` also creates a fresh universe in the body of a definition.
The cleanest fix is Option A.

### Mathematical faithfulness:
The LaTeX definition says "the set of symmetries of **something**" — it doesn't constrain the universe of "something". In standard mathematics, there's no notion of universe levels. However, the Lean formalization must pick a specific universe for the existential, and using the same universe as `G` is the standard and correct choice (as done in Mathlib's Cayley theorem formalization).
