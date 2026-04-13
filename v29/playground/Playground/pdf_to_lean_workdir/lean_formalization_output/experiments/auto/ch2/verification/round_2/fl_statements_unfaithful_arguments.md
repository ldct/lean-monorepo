# Chapter 2 — Unfaithful Statement Arguments (Round 2)

## Ch2_theorem_5 — Universe Mismatch in Forward Direction

### LaTeX quote:
```
\begin{theorem}[Proposition 2.2]
More generally, for a ring $R$, suppose $e \in R$ is idempotent. Then we have:
\[ R = eR \oplus (1 - e)R \]
both of which are rings. Conversely, in $A \times B$, $(1, 0)$ is idempotent. So the presence of idempotents is equivalent to the ring splitting as a product.
\end{theorem}
```

### Current Lean statement:
```lean
theorem Ch2_theorem_5 :
    (∀ (R : Type*) [CommRing R] (e : R), e * e = e →
      ∃ (A B : Type*) (_ : Ring A) (_ : Ring B) (f : R ≃+* A × B), f e = (1, 0)) ∧
    (∀ (A B : Type*) [Ring A] [Ring B],
      ((1 : A), (0 : B)) * ((1 : A), (0 : B)) = ((1 : A), (0 : B)))
```

### Issue:
The existential `∃ (A B : Type*) ...` in the forward direction introduces fresh universe parameters `u_2` and `u_3` for types A and B, independent of R's universe `u_1`. The natural witnesses `A = R ⧸ Ideal.span {1-e}` and `B = R ⧸ Ideal.span {e}` are both in `Type u_1` (R's universe), so they cannot fill the existential when `u_2 ≠ u_1` or `u_3 ≠ u_1`.

This is confirmed by minimal test: even `example : ∀ (R : Type*), ∃ (A : Type*), A = R := sorry` is unprovable because the existential introduces a separate universe parameter.

### Suggested fix:
Use the same universe for R, A, and B. Either:
1. `∀ (R : Type u) [CommRing R] (e : R), ... ∃ (A B : Type u) ...`
2. Or restructure to avoid the existential entirely, e.g., directly state the decomposition `R ≃+* (R ⧸ Ideal.span {1-e}) × (R ⧸ Ideal.span {e})`

### Note on the mathematical proof:
The mathematical proof works perfectly using `RingHom.prod_bijective_of_isIdempotentElem` from Mathlib. The only blocker is the universe mismatch in the statement.
