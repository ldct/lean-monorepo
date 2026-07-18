# Plan: computable coset theory for `FiniteGroup.lean`

Goal: extend the from-scratch `FiniteGroup.Group` / `BSubgroup` development with a
**computable, compilable** theory of cosets — e.g. `#eval g * C` on a coset `C`
returns another coset.

## Design decisions

- **Coset representation:** a structure whose *data* is a `Finset G` and whose
  *proof of being a coset* is a `Prop` field. Props are erased at runtime, so the
  type stays fully computable. (Rejected: bare `Finset G` — loses the invariant;
  quotient type `G ⧸ H` — computable but `Repr`/`#eval` gets awkward.)
- **`DecidableEq G`:** required after all — `Finset.image` needs it to build
  `g • H`. Keep it, but prefer attaching it to coset definitions rather than the
  `Group` class itself.
- **`#eval` prerequisites:** `Repr G` plus a concrete computable group instance
  as a test bed.
- **Caveat driving the roadmap:** `g * C` (element × coset) is always
  well-defined; `C₁ * C₂` (coset × coset) is well-defined only for **normal** `H`.
  Quotient groups therefore come last.

## Stage 1 — left cosets

```lean
def lcoset (g : G) (H : BSubgroup G) : Finset G :=
  H.carrier.image (g * ·)

structure LeftCoset (H : BSubgroup G) where
  carrier  : Finset G
  is_coset : ∃ g, carrier = lcoset g H    -- Prop ⇒ erased, stays computable
```

- [x] `lcoset`, `LeftCoset`, `LeftCoset.of g H` constructor
- [x] `instance : HMul G (LeftCoset H) (LeftCoset H)` — witness is `g * (C's witness)`
- [x] `instance [Repr G] : Repr (LeftCoset H)` — delegate to `carrier`
- [x] `LeftCoset.ext` (cosets equal iff carriers equal) → `DecidableEq (LeftCoset H)`

## Stage 2 — basic lemmas (forced by Stage 1 proofs)

- [x] Derive `mul_left_cancel` / `mul_right_cancel` from the five group axioms
- [x] `(g * ·)` is injective ⇒ `(lcoset g H).card = H.carrier.card` (`Finset.card_image_of_injective`)
- [x] Equality criterion: `lcoset g H = lcoset k H ↔ g⁻¹ * k ∈ H.carrier`
- [x] Membership: `g ∈ lcoset g H`; cosets are disjoint or equal

## Stage 3 — concrete group + `#eval` demos

- [x] Small computable instance: cyclic group on `Fin n`, or S₃ via multiplication
  table with `deriving DecidableEq, Repr`
- [x] A `BSubgroup` of it, and working `#eval g * LeftCoset.of a H` examples

## Stage 4 — Lagrange

- [x] Cosets partition the group (needs a `Fintype G` or finite-carrier setting)
- [x] `|G| = |H| * (number of cosets)`

## Stage 5 — normal subgroups and computable quotients

- [x] `IsNormal H` predicate
- [x] `C₁ * C₂` well-defined for normal `H`; `#eval C₁ * C₂` works
- [x] Quotient group structure on cosets (`Group (LeftCoset H)` when `H` normal)
