# Chapter 1: Formal Statement Verification Results (Round 1)

## Coverage Check

**Result: PASS**

```
Total theorem blocks:  11
Found (exactly once):  11
Missing:               0
Duplicates:            0
Coverage:              100.0%
ADJACENCY: PASS - All comment blocks immediately followed by correctly named declarations
RESULT: COMPLETE - All statements found exactly once, all adjacent!
```

## Build Check

**Result: PASS**

Build completed successfully. Only warnings present (two `sorry` usages and long-line linter warnings). No errors.

## Per-Statement Semantic Equivalence Assessment

---

### Ch1_def_1 — Definition 1.1 (Concrete group)

**LaTeX:** A set G is a group iff it is the set of symmetries of something.

**Natural Language:** G is a concrete group if there exists a type S and an injective group homomorphism from G into the group of permutations of S.

**Lean:**
```lean
def Ch1_def_1 (G : Type*) [Group G] : Prop :=
  ∃ (S : Type*), ∃ (f : G →* Equiv.Perm S), Function.Injective f
```

**Mathlib definitions checked:**
- `Equiv.Perm S` = `S ≃ S`, the type of bijections from S to itself. Has a `Group` instance (`Equiv.Perm.permGroup`). Correctly models "group of permutations of S".
- `G →*` = `MonoidHom`, preserves multiplication and identity. On groups, this is a group homomorphism.
- `Function.Injective f` means `f x = f y → x = y`.

**A. LaTeX -> NL:** The LaTeX says "set of symmetries of something," which mathematically means G is (isomorphic to) a subgroup of Perm(S). The NL interprets this as the existence of an injective group homomorphism into Perm(S), which is the standard formalization of "being isomorphic to a subgroup." Faithful.

**B. NL -> Lean:** The Lean directly encodes: there exists a type S and an injective MonoidHom from G to Equiv.Perm S. This exactly matches the NL. Faithful.

**C. Overall: Equivalent**

---

### Ch1_def_2 — Definition 1.2 (Abstract group)

**LaTeX:** A set G with a binary operation is a group iff: (1) ∃ identity e with ea = ae = a, (2) ∃ inverses with aa⁻¹ = a⁻¹a = e, (3) associativity a(bc) = (ab)c.

**Natural Language:** Same as LaTeX.

**Lean:**
```lean
def Ch1_def_2 (G : Type*) [Mul G] : Prop :=
  (∃ e : G, (∀ a : G, e * a = a ∧ a * e = a) ∧
    (∀ a : G, ∃ a_inv : G, a * a_inv = e ∧ a_inv * a = e)) ∧
  (∀ a b c : G, a * (b * c) = (a * b) * c)
```

**A. LaTeX -> NL:** Faithful. All three conditions are preserved.

**B. NL -> Lean:**
- Uses `[Mul G]` to provide only a binary operation (not assuming group structure). Correct.
- Identity: `∃ e, ∀ a, e * a = a ∧ a * e = a`. Correctly captures two-sided identity. ✓
- Inverses: nested under the same `∃ e`, so inverses are w.r.t. the same identity element. `∀ a, ∃ a_inv, a * a_inv = e ∧ a_inv * a = e`. Correctly captures two-sided inverses. ✓
- Associativity: `∀ a b c, a * (b * c) = (a * b) * c`. ✓

**C. Overall: Equivalent**

---

### Ch1_def_3 — Definition 1.3 (Subgroup)

**LaTeX:** H ⊆ G is a subgroup iff it contains the identity, is closed under composition, and contains all inverses.

**Natural Language:** Same as LaTeX.

**Lean:**
```lean
def Ch1_def_3 (G : Type*) [Group G] (H : Set G) : Prop :=
  (1 : G) ∈ H ∧
  (∀ a b : G, a ∈ H → b ∈ H → a * b ∈ H) ∧
  (∀ a : G, a ∈ H → a⁻¹ ∈ H)
```

**A. LaTeX -> NL:** Faithful.

**B. NL -> Lean:**
- `H : Set G` models H as a subset of G. ✓
- `(1 : G) ∈ H`: identity membership. In Lean's `Group`, `1` is the identity element. ✓
- Closure under operation: `∀ a b, a ∈ H → b ∈ H → a * b ∈ H`. ✓
- Inverse closure: `∀ a, a ∈ H → a⁻¹ ∈ H`. ✓

**C. Overall: Equivalent**

---

### Ch1_def_4 — Definition 1.4 (Homomorphism)

**LaTeX:** f : G → H is a homomorphism iff for all a, b ∈ G, f(ab) = f(a)f(b).

**Natural Language:** Same as LaTeX.

**Lean:**
```lean
def Ch1_def_4 (G H : Type*) [Group G] [Group H] (f : G → H) : Prop :=
  ∀ a b : G, f (a * b) = f a * f b
```

**A. LaTeX -> NL:** Faithful.

**B. NL -> Lean:** The Lean statement directly encodes `∀ a b, f(a * b) = f(a) * f(b)` for a plain function `f : G → H`. Both G and H have `[Group]` instances. ✓

**C. Overall: Equivalent**

---

### Ch1_theorem_5 — Proposition 1.1 (Homomorphisms preserve inverses and identity)

**LaTeX:** Homomorphisms preserve inverses and the identity.

**Natural Language:** If f : G → H is a group homomorphism, then f(e) = e and f(a⁻¹) = f(a)⁻¹ for all a ∈ G.

**Lean:**
```lean
theorem Ch1_theorem_5 (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f 1 = 1 ∧ ∀ g : G, f g⁻¹ = (f g)⁻¹ := by
  sorry
```

**Mathlib definitions checked:**
- `G →* H` = `MonoidHom G H`, which bundles a function `G → H` with proof that it preserves `*` and `1`. This is a group homomorphism when G and H are groups.

**A. LaTeX -> NL:** The LaTeX is terse ("preserves inverses and the identity"). The NL correctly expands this to the two concrete statements: f(e) = e and f(a⁻¹) = f(a)⁻¹. Faithful.

**B. NL -> Lean:**
- `f 1 = 1`: f preserves the identity. ✓
- `∀ g, f g⁻¹ = (f g)⁻¹`: f preserves inverses. ✓
- Note: `f : G →* H` (MonoidHom) already bundles the homomorphism property. The theorem states additional consequences. This is correct — the theorem says "if f is a homomorphism, then these hold." Using `→*` as the type of f captures the hypothesis.

**C. Overall: Equivalent**

---

### Ch1_def_6 — Definition 1.5 (Isomorphism)

**LaTeX:** A homomorphism is an isomorphism iff it is a bijection.

**Natural Language:** A group homomorphism f : G → H is an isomorphism iff f is a bijection.

**Lean:**
```lean
def Ch1_def_6 (G H : Type*) [Group G] [Group H] (f : G →* H) : Prop :=
  Function.Bijective f
```

**Mathlib definitions checked:**
- `Function.Bijective f` = `Function.Injective f ∧ Function.Surjective f`. Standard bijection.

**A. LaTeX -> NL:** Faithful.

**B. NL -> Lean:** `f : G →* H` captures "group homomorphism." `Function.Bijective f` captures "is a bijection." ✓

**C. Overall: Equivalent**

---

### Ch1_def_7 — Definition 1.6 (Endomorphism)

**LaTeX:** A homomorphism is an endomorphism iff it has the same domain as its codomain.

**Natural Language:** A group homomorphism is an endomorphism iff it has the same domain as its codomain, i.e., it is a homomorphism from G to G.

**Lean:**
```lean
def Ch1_def_7 (G : Type*) [Group G] := G →* G
```

**A. LaTeX -> NL:** Faithful.

**B. NL -> Lean:** `G →* G` is the type of group homomorphisms from G to G. This defines the type of endomorphisms of G, which correctly captures "a homomorphism with the same domain and codomain." ✓

**C. Overall: Equivalent**

---

### Ch1_def_8 — Definition 1.7 (Automorphism)

**LaTeX:** A homomorphism is an automorphism iff it is an isomorphism and an endomorphism.

**Natural Language:** A group homomorphism is an automorphism iff it is both an isomorphism (bijective) and an endomorphism (domain equals codomain), i.e., it is a bijective homomorphism from G to G.

**Lean:**
```lean
def Ch1_def_8 (G : Type*) [Group G] := G ≃* G
```

**Mathlib definitions checked:**
- `MulEquiv M N` (notation `M ≃* N`) = the type of an equiv `M ≃ N` which preserves multiplication. An equiv is a bijection (function + inverse + left/right inverse proofs). MulEquiv bundles: an equivalence (bijection) that is also a multiplicative homomorphism. This exactly captures "bijective group homomorphism from G to G."

**A. LaTeX -> NL:** Faithful.

**B. NL -> Lean:** `G ≃* G` is the type of multiplicative equivalences from G to G, i.e., bijective group homomorphisms from G to G. This is exactly an automorphism. ✓

**C. Overall: Equivalent**

---

### Ch1_def_9 — Definition 1.8 (Left action)

**LaTeX:** A map · : G × S → S is a left action iff: (1) g · (h · s) = (gh) · s, (2) e · s = s. (Also mentions right actions as satisfying analogous properties.)

**Natural Language:** Same as LaTeX but only for left actions (the right action remark is omitted).

**Lean:**
```lean
def Ch1_def_9 (G : Type*) [Group G] (S : Type*) (smul : G → S → S) : Prop :=
  (∀ g h : G, ∀ s : S, smul g (smul h s) = smul (g * h) s) ∧
  (∀ s : S, smul 1 s = s)
```

**A. LaTeX -> NL:** The NL omits the parenthetical remark about right actions. Since the definition is titled "Left action" and the right action is only mentioned as an aside, this omission is acceptable. Faithful for left actions.

**B. NL -> Lean:**
- `smul : G → S → S` is the action map (curried form of G × S → S). ✓
- `∀ g h s, smul g (smul h s) = smul (g * h) s`: compatibility. ✓
- `∀ s, smul 1 s = s`: identity action. ✓ (`1` is the identity in the Group instance.)

**C. Overall: Equivalent**

---

### Ch1_def_10 — Definition 1.9 (G-set)

**LaTeX:** S is a G-set iff we have an action of G on S which is a homomorphism π : G → Perm(S).

**Natural Language:** S is a G-set iff there exists a group homomorphism π : G → Perm(S).

**Lean:**
```lean
def Ch1_def_10 (G : Type*) [Group G] (S : Type*) : Prop :=
  ∃ (_ : G →* Equiv.Perm S), True
```

**Mathlib definitions checked:**
- `G →* Equiv.Perm S`: group homomorphism from G to the permutation group of S. This is exactly a group action expressed as a homomorphism.
- `Equiv.Perm S` has a `Group` instance.

**A. LaTeX -> NL:** The LaTeX says "an action of G on S which is a homomorphism π : G → Perm(S)." The NL says "there exists a group homomorphism π : G → Perm(S)." These are equivalent: a group action on S is the same data as a homomorphism G → Perm(S). Faithful.

**B. NL -> Lean:** `∃ (_ : G →* Equiv.Perm S), True` asserts existence of a group homomorphism from G to Equiv.Perm S. The `True` is stylistically unusual (could be `Nonempty (G →* Equiv.Perm S)` instead), but semantically equivalent — the existential is not vacuous. ✓

**C. Overall: Equivalent**

---

### Ch1_theorem_11 — Theorem 1.1 (Abstract group iff concrete group)

**LaTeX:** A set G is an abstract group iff it is a concrete group.

**Natural Language:** A set G is an abstract group if and only if it is a concrete group. That is, every abstract group can be realized as a group of permutations (Cayley's theorem), and conversely.

**Lean:**
```lean
theorem Ch1_theorem_11 (G : Type*) [Group G] : Ch1_def_1 G := by
  sorry
```

**A. LaTeX -> NL:** Faithful. The NL correctly expands the iff into both directions.

**B. NL -> Lean:** The LaTeX/NL state an "iff", but the Lean formalization only states one direction: `[Group G] → Ch1_def_1 G` (abstract group implies concrete group, i.e., Cayley's theorem). The reverse direction ("concrete group implies abstract group") is not explicitly stated.

However, since `Ch1_def_1` is defined as `def Ch1_def_1 (G : Type*) [Group G] : Prop := ...`, it already requires `[Group G]` (abstract group) in its signature. This means `Ch1_def_1 G` can only be stated for types that are already abstract groups. The converse direction is thus trivially embedded in the type-theoretic setup: any G satisfying `Ch1_def_1` must already be an abstract group by the definition's own requirements.

While this is a valid encoding choice in dependent type theory, the theorem as stated is strictly only one direction (Cayley's theorem). The "iff" nature is split between the definition and the theorem rather than being explicit in the theorem statement.

**C. Overall: Minor discrepancy**

The theorem only explicitly states one direction of the "iff." The converse is trivially true due to the definition of `Ch1_def_1` requiring `[Group G]`, so no mathematical content is lost, but the statement does not syntactically express the biconditional that the original theorem asserts.

---

## Summary

| # | Name | Statement | Rating |
|---|------|-----------|--------|
| 1 | Ch1_def_1 | Definition 1.1 (Concrete group) | **Equivalent** |
| 2 | Ch1_def_2 | Definition 1.2 (Abstract group) | **Equivalent** |
| 3 | Ch1_def_3 | Definition 1.3 (Subgroup) | **Equivalent** |
| 4 | Ch1_def_4 | Definition 1.4 (Homomorphism) | **Equivalent** |
| 5 | Ch1_theorem_5 | Proposition 1.1 (Preserves inverses/identity) | **Equivalent** |
| 6 | Ch1_def_6 | Definition 1.5 (Isomorphism) | **Equivalent** |
| 7 | Ch1_def_7 | Definition 1.6 (Endomorphism) | **Equivalent** |
| 8 | Ch1_def_8 | Definition 1.7 (Automorphism) | **Equivalent** |
| 9 | Ch1_def_9 | Definition 1.8 (Left action) | **Equivalent** |
| 10 | Ch1_def_10 | Definition 1.9 (G-set) | **Equivalent** |
| 11 | Ch1_theorem_11 | Theorem 1.1 (Cayley's theorem) | **Minor discrepancy** |

**Total statements checked:** 11
**Equivalent:** 10
**Minor discrepancies:** 1
**Major discrepancies:** 0

## Statements Requiring Re-formalization

1. **Ch1_theorem_11 (Theorem 1.1):** The original theorem states an "if and only if" (abstract group ↔ concrete group), but the Lean formalization only explicitly states one direction (`[Group G] → Ch1_def_1 G`). While the converse is trivially true due to the definition of `Ch1_def_1` requiring `[Group G]`, the biconditional should be made explicit in the theorem statement to faithfully represent the original theorem. A possible fix would be to reformulate `Ch1_def_1` to not require `[Group G]` and then state the theorem as an iff, or alternatively state the theorem as an iff using `Ch1_def_2` for the abstract group side.
