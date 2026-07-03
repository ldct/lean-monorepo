import Mathlib

namespace OrderOfSimproc

/-!
# Simproc for `orderOf g = n`

Rewrites `orderOf g = n` (for concrete `n ≥ 2`) to the equivalent conjunction:
  `g ^ n = 1 ∧ g ^ (n / p₁) ≠ 1 ∧ ... ∧ g ^ (n / pₖ) ≠ 1`
where `p₁, ..., pₖ` are the prime factors of `n`.

After the simproc fires, the remaining goals involve concrete group element
computations that can be closed by `decide` or `native_decide`.
-/

-- ============================================================
-- Parametric iff lemmas for 1-4 prime factors
-- ============================================================

private theorem fwd_ne {G : Type*} [Group G] {g : G} {n d : ℕ}
    (h : orderOf g = n) (hndvd : ¬(n ∣ d)) :
    g ^ d ≠ 1 :=
  fun habs => hndvd (h ▸ orderOf_dvd_of_pow_eq_one habs)

private theorem bwd_core {G : Type*} [Group G] {g : G} {n : ℕ}
    (hn : 0 < n) (hpow : g ^ n = 1)
    (hforall : ∀ p, Nat.Prime p → p ∣ n → g ^ (n / p) ≠ 1) :
    orderOf g = n :=
  orderOf_eq_of_pow_and_pow_div_prime hn hpow hforall

theorem orderOf_eq_iff_one_prime {G : Type*} [Group G] (g : G) (n p₁ : ℕ)
    (hn : 0 < n) (hnd₁ : ¬(n ∣ n / p₁))
    (hclass : ∀ k, k ≤ n → Nat.Prime k → k ∣ n → k = p₁) :
    orderOf g = n ↔ g ^ n = 1 ∧ g ^ (n / p₁) ≠ 1 := by
  constructor
  · exact fun h => ⟨h ▸ pow_orderOf_eq_one g, fwd_ne h hnd₁⟩
  · intro ⟨h0, h1⟩
    exact bwd_core hn h0 fun p hp hpn => by
      have := hclass p (Nat.le_of_dvd hn hpn) hp hpn; subst this; exact h1

theorem orderOf_eq_iff_two_primes {G : Type*} [Group G] (g : G) (n p₁ p₂ : ℕ)
    (hn : 0 < n) (hnd₁ : ¬(n ∣ n / p₁)) (hnd₂ : ¬(n ∣ n / p₂))
    (hclass : ∀ k, k ≤ n → Nat.Prime k → k ∣ n → k = p₁ ∨ k = p₂) :
    orderOf g = n ↔ g ^ n = 1 ∧ g ^ (n / p₁) ≠ 1 ∧ g ^ (n / p₂) ≠ 1 := by
  constructor
  · exact fun h => ⟨h ▸ pow_orderOf_eq_one g, fwd_ne h hnd₁, fwd_ne h hnd₂⟩
  · intro ⟨h0, h1, h2⟩
    exact bwd_core hn h0 fun p hp hpn => by
      rcases hclass p (Nat.le_of_dvd hn hpn) hp hpn with rfl | rfl <;> assumption

theorem orderOf_eq_iff_three_primes {G : Type*} [Group G] (g : G) (n p₁ p₂ p₃ : ℕ)
    (hn : 0 < n) (hnd₁ : ¬(n ∣ n / p₁)) (hnd₂ : ¬(n ∣ n / p₂)) (hnd₃ : ¬(n ∣ n / p₃))
    (hclass : ∀ k, k ≤ n → Nat.Prime k → k ∣ n → k = p₁ ∨ k = p₂ ∨ k = p₃) :
    orderOf g = n ↔ g ^ n = 1 ∧ g ^ (n / p₁) ≠ 1 ∧ g ^ (n / p₂) ≠ 1 ∧ g ^ (n / p₃) ≠ 1 := by
  constructor
  · exact fun h => ⟨h ▸ pow_orderOf_eq_one g, fwd_ne h hnd₁, fwd_ne h hnd₂, fwd_ne h hnd₃⟩
  · intro ⟨h0, h1, h2, h3⟩
    exact bwd_core hn h0 fun p hp hpn => by
      rcases hclass p (Nat.le_of_dvd hn hpn) hp hpn with rfl | rfl | rfl <;> assumption

theorem orderOf_eq_iff_four_primes {G : Type*} [Group G] (g : G) (n p₁ p₂ p₃ p₄ : ℕ)
    (hn : 0 < n) (hnd₁ : ¬(n ∣ n / p₁)) (hnd₂ : ¬(n ∣ n / p₂))
    (hnd₃ : ¬(n ∣ n / p₃)) (hnd₄ : ¬(n ∣ n / p₄))
    (hclass : ∀ k, k ≤ n → Nat.Prime k → k ∣ n → k = p₁ ∨ k = p₂ ∨ k = p₃ ∨ k = p₄) :
    orderOf g = n ↔ g ^ n = 1 ∧ g ^ (n / p₁) ≠ 1 ∧ g ^ (n / p₂) ≠ 1
      ∧ g ^ (n / p₃) ≠ 1 ∧ g ^ (n / p₄) ≠ 1 := by
  constructor
  · exact fun h => ⟨h ▸ pow_orderOf_eq_one g, fwd_ne h hnd₁, fwd_ne h hnd₂,
      fwd_ne h hnd₃, fwd_ne h hnd₄⟩
  · intro ⟨h0, h1, h2, h3, h4⟩
    exact bwd_core hn h0 fun p hp hpn => by
      rcases hclass p (Nat.le_of_dvd hn hpn) hp hpn with rfl | rfl | rfl | rfl <;> assumption

-- ============================================================
-- Simproc implementation
-- ============================================================

/-- Compute prime factors of a natural number. -/
def natPrimeFactors (n : ℕ) : List ℕ :=
  if n < 2 then []
  else
    let rec go (n : ℕ) (p : ℕ) (acc : List ℕ) (fuel : ℕ) : List ℕ :=
      if fuel = 0 then acc
      else if n < 2 then acc
      else if p * p > n then
        if acc.contains n then acc else acc ++ [n]
      else if n % p = 0 then
        let acc' := if acc.contains p then acc else acc ++ [p]
        go (n / p) p acc' (fuel - 1)
      else
        go n (p + 1) acc (fuel - 1)
    go n 2 [] (n + 1)

open Lean Meta in
simproc_decl orderOfSimproc (orderOf _ = _) := fun e => do
  let some (_, lhs, rhs) := e.eq? | return .continue
  let_expr orderOf _ _ g ← lhs | return .continue
  let some n ← Nat.fromExpr? rhs | return .continue
  if n < 2 then return .continue
  let primes := natPrimeFactors n
  if primes.length == 0 || primes.length > 4 then return .continue
  let nExpr := mkNatLit n

  -- Prove 0 < n by decide
  let posProof ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, nExpr])

  -- Prove ¬(n ∣ n / pᵢ) by decide for each prime
  let mut ndProofs : Array Expr := #[]
  for p in primes do
    let ndType ← mkAppM ``Not #[← mkAppM ``Dvd.dvd #[nExpr, mkNatLit (n / p)]]
    ndProofs := ndProofs.push (← mkDecideProof ndType)

  -- Prove classification lemma by decide
  -- ∀ k, k ≤ n → Prime k → k ∣ n → k = p₁ ∨ ... ∨ k = pₖ
  let classProof ← do
    withLocalDeclD `k (mkConst ``Nat) fun k => do
      let leType ← mkAppM ``LE.le #[k, nExpr]
      let primeType ← mkAppM ``Nat.Prime #[k]
      let dvdType ← mkAppM ``Dvd.dvd #[k, nExpr]
      let mut orType ← mkAppM ``Eq #[k, mkNatLit primes.getLast!]
      for p in primes.dropLast.reverse do
        orType ← mkAppM ``Or #[← mkAppM ``Eq #[k, mkNatLit p], orType]
      let body ← mkArrow leType (← mkArrow primeType (← mkArrow dvdType orType))
      let classType ← mkForallFVars #[k] body
      mkDecideProof classType

  -- Apply the appropriate lemma
  let primeExprs := primes.map mkNatLit
  let iffProof ←
    if primes.length == 1 then
      mkAppM ``orderOf_eq_iff_one_prime
        #[g, nExpr, primeExprs[0]!, posProof, ndProofs[0]!, classProof]
    else if primes.length == 2 then
      mkAppM ``orderOf_eq_iff_two_primes
        #[g, nExpr, primeExprs[0]!, primeExprs[1]!, posProof,
          ndProofs[0]!, ndProofs[1]!, classProof]
    else if primes.length == 3 then
      mkAppM ``orderOf_eq_iff_three_primes
        #[g, nExpr, primeExprs[0]!, primeExprs[1]!, primeExprs[2]!, posProof,
          ndProofs[0]!, ndProofs[1]!, ndProofs[2]!, classProof]
    else if primes.length == 4 then
      mkAppM ``orderOf_eq_iff_four_primes
        #[g, nExpr, primeExprs[0]!, primeExprs[1]!, primeExprs[2]!, primeExprs[3]!,
          posProof, ndProofs[0]!, ndProofs[1]!, ndProofs[2]!, ndProofs[3]!, classProof]
    else
      return .continue

  let propextProof ← mkAppM ``propext #[iffProof]
  let propextType ← inferType propextProof
  let some (_, _, rhs') := propextType.eq? | return .continue
  return .visit {
    expr := rhs',
    proof? := some propextProof
  }

-- ============================================================
-- Tests
-- ============================================================

-- Basic: abstract group, order 6
example {G : Type*} [Group G] (g : G)
    (h6 : g ^ 6 = 1) (h3 : g ^ 3 ≠ 1) (h2 : g ^ 2 ≠ 1) :
    orderOf g = 6 := by
  simp only [orderOfSimproc]
  exact ⟨h6, h3, h2⟩

-- Basic: abstract group, order 12
example {G : Type*} [Group G] (g : G)
    (h12 : g ^ 12 = 1) (h6 : g ^ 6 ≠ 1) (h4 : g ^ 4 ≠ 1) :
    orderOf g = 12 := by
  simp only [orderOfSimproc]
  exact ⟨h12, h6, h4⟩

-- order 30 = 2 × 3 × 5 (three prime factors)
example {G : Type*} [Group G] (g : G)
    (h30 : g ^ 30 = 1) (h15 : g ^ 15 ≠ 1) (h10 : g ^ 10 ≠ 1) (h6 : g ^ 6 ≠ 1) :
    orderOf g = 30 := by
  simp only [orderOfSimproc]
  exact ⟨h30, h15, h10, h6⟩

-- In hypothesis position
example {G : Type*} [Group G] (g : G) (h : orderOf g = 6) : g ^ 6 = 1 := by
  simp only [orderOfSimproc] at h
  exact h.1

-- Prime order (one prime factor): n/p produces 5/5 in the iff
example {G : Type*} [Group G] (g : G) (h5 : g ^ 5 = 1) (h1 : g ≠ 1) :
    orderOf g = 5 := by
  simp only [orderOfSimproc]
  -- goal is g ^ 5 = 1 ∧ g ^ (5 / 5) ≠ 1, need norm_num to reduce 5/5
  exact ⟨h5, by simpa using h1⟩

-- Concrete: DihedralGroup.r 2 in DihedralGroup 12 has order 6
example : orderOf (DihedralGroup.r (2 : ZMod 12)) = 6 := by
  simp only [orderOfSimproc]
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- User's desired pattern: simp only [orderOfSimproc] <;> native_decide
example : orderOf (DihedralGroup.r (2 : ZMod 12)) = 6 := by
  simp only [orderOfSimproc]
  decide

-- Another dihedral group example: order 12 (prime factors 2, 3)
example : orderOf (DihedralGroup.r (1 : ZMod 12)) = 12 := by
  simp only [orderOfSimproc]
  decide

end OrderOfSimproc
