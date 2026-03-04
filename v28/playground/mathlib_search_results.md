# Mathlib Search Results

## 1. `Nat.card` of `alternatingGroup`

**File:** `Mathlib/GroupTheory/SpecificGroups/Alternating.lean`

```lean
-- Line 121
theorem two_mul_nat_card_alternatingGroup [Nontrivial α] :
    2 * Nat.card (alternatingGroup α) = Nat.card (Perm α)

-- Line 125
theorem two_mul_card_alternatingGroup [Nontrivial α] :
    2 * card (alternatingGroup α) = card (Perm α)

-- Line 129
theorem card_alternatingGroup [Nontrivial α] :
    card (alternatingGroup α) = (card α).factorial / 2

-- Line 133
theorem nat_card_alternatingGroup [Nontrivial α] :
    Nat.card (alternatingGroup α) = (Nat.card α).factorial / 2
```

**File:** `Mathlib/GroupTheory/SpecificGroups/Alternating/KleinFour.lean`

```lean
theorem card_of_card_eq_four (hα4 : Nat.card α = 4) :
    Nat.card (alternatingGroup α) = 12
```

## 2. `alternatingGroup` not being cyclic

There is **no direct** `not_isCyclic` theorem for `alternatingGroup` in Mathlib. However, there are related results:

**Center is trivial** (from `Alternating.lean` line 389):
```lean
theorem center_eq_bot (hα4 : 4 ≤ Nat.card α) :
    Subgroup.center (alternatingGroup α) = ⊥
```

**Klein Four subgroup** (from `Alternating/KleinFour.lean`):
```lean
theorem kleinFour_isKleinFour (hα4 : Nat.card α = 4) :
    IsKleinFour (kleinFour α)
```

**`IsKleinFour.not_isCyclic`** (from `KleinFour.lean` line 88):
```lean
lemma not_isCyclic : ¬IsCyclic G  -- for any G satisfying IsKleinFour
```

So one can show `alternatingGroup (Fin 4)` is not cyclic indirectly:
- Its card is 12, and it contains a Klein Four subgroup (exponent 2, card 4)
- Or: its center is trivial (for |α| ≥ 4), so it's not abelian, hence not cyclic

## 3. `DihedralGroup` cardinality

**File:** `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean`

```lean
-- Line 145
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n

-- Line 148
theorem nat_card : Nat.card (DihedralGroup n) = 2 * n
```

Also available:
```lean
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val
theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2

lemma not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)
lemma isCyclic_iff : IsCyclic (DihedralGroup n) ↔ n = 1
```

## 4. Element orders in `alternatingGroup (Fin 4)`

There is **no direct theorem** listing element orders in `alternatingGroup (Fin 4)`. However:

**From `Alternating/KleinFour.lean`:**
```lean
-- Elements of the Klein Four subgroup have cycle type () or (2,2)
theorem mem_kleinFour_of_order_two_pow (hα4 : Nat.card α = 4) {g : Perm α}
    (hg0 : g ∈ alternatingGroup α) {n : ℕ} (hg : orderOf g ∣ 2 ^ n) :
    g.cycleType = { } ∨ g.cycleType = {2, 2}

-- The Klein Four subgroup has exponent 2
theorem exponent_kleinFour_of_card_eq_four (hα4 : Nat.card α = 4) :
    Monoid.exponent (kleinFour α) = 2

-- kleinFour has 4 elements = {identity} ∪ {elements with cycle type (2,2)}
theorem coe_kleinFour_of_card_eq_four (hα4 : Nat.card α = 4) :
    (kleinFour α : Set (alternatingGroup α)) =
      {1} ∪ {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2}}

-- The quotient alternatingGroup(Fin 4) / kleinFour has card 3
-- (hence elements outside kleinFour have order 3)
```

From the structure:
- `alternatingGroup (Fin 4)` has 12 elements
- 1 identity (order 1)
- 3 elements of cycle type (2,2) (order 2) — the Klein Four subgroup minus identity  
- 8 elements of order 3 (3-cycles)

## Summary of key theorem names for imports:

| Theorem | Full name |
|---|---|
| Alt group card | `Equiv.Perm.nat_card_alternatingGroup` |
| Alt group Fin 4 card | `alternatingGroup.card_of_card_eq_four` |
| Dihedral card | `DihedralGroup.nat_card` |
| Dihedral not cyclic | `DihedralGroup.not_isCyclic` |
| Klein Four not cyclic | `IsKleinFour.not_isCyclic` |
| Alt center trivial | `Equiv.Perm.alternatingGroup.center_eq_bot` |
| Klein Four in Alt(4) | `alternatingGroup.kleinFour_isKleinFour` |
| Klein Four exponent | `alternatingGroup.exponent_kleinFour_of_card_eq_four` |
