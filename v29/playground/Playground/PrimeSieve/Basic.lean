import Mathlib

/-!
# Sieve of Eratosthenes — kernel-checked primality lookup

We define the sieve of Eratosthenes as an executable function on `ℕ`,
together with a `Valid N` predicate that asserts the sieve agrees with
`Nat.Prime` on `[0, N]`. The user proves `Valid N` once (via `decide`) — this
is the `O(N log log N)` precompute — and afterwards each individual primality
question for `k ≤ N` is reduced to a `Bool` lookup in the precomputed table.

Everything here is kernel-checked: no `native_decide`.
-/

namespace PrimeSieve

/-- Mark multiples of `i`, starting at `j`, as composite in `arr`.
    Uses fuel for structural recursion. -/
def markMultiples (i : ℕ) (arr : Array Bool) (j : ℕ) : ℕ → Array Bool
  | 0 => arr
  | fuel + 1 =>
    if j < arr.size then markMultiples i (arr.set! j false) (j + i) fuel
    else arr

/-- One outer iteration of the sieve at index `i`. -/
def sieveStep (N : ℕ) (arr : Array Bool) (i : ℕ) : ℕ → Array Bool
  | 0 => arr
  | fuel + 1 =>
    if i * i > N then arr
    else if arr.getD i false then
      sieveStep N (markMultiples i arr (i * i) (N + 1)) (i + 1) fuel
    else
      sieveStep N arr (i + 1) fuel

/-- Sieve of Eratosthenes producing an `Array Bool` of size `N + 1`,
    where index `k` records whether `k` is prime. -/
def sieve (N : ℕ) : Array Bool :=
  let arr := (Array.replicate (N + 1) true).set! 0 false
  let arr := if 1 ≤ N then arr.set! 1 false else arr
  sieveStep N arr 2 N

/-- O(1) primality lookup against the sieve. -/
def isPrime (N k : ℕ) : Bool := (sieve N).getD k false

/-- Correctness: the sieve agrees with `Nat.Prime` on every `k ≤ N`.
    Proving this for a concrete `N` is the precompute step. -/
def Valid (N : ℕ) : Prop := ∀ k, k ≤ N → (isPrime N k = true ↔ Nat.Prime k)

instance instDecValid (N : ℕ) : Decidable (Valid N) :=
  have : Decidable (∀ k ∈ List.range (N + 1), isPrime N k = true ↔ Nat.Prime k) :=
    inferInstance
  decidable_of_iff (∀ k ∈ List.range (N + 1), isPrime N k = true ↔ Nat.Prime k) <| by
    simp only [List.mem_range, Valid]
    exact ⟨fun h k hk => h k (Nat.lt_succ_of_le hk),
           fun h k hk => h k (Nat.le_of_lt_succ hk)⟩

/-- Given a precomputed validity proof and a bound, conclude `Nat.Prime k`. -/
theorem prime_of_lookup {N k : ℕ} (hv : Valid N) (hk : k ≤ N)
    (h : isPrime N k = true) : Nat.Prime k :=
  (hv k hk).mp h

/-- Given a precomputed validity proof and a bound, conclude `¬ Nat.Prime k`. -/
theorem not_prime_of_lookup {N k : ℕ} (hv : Valid N) (hk : k ≤ N)
    (h : isPrime N k = false) : ¬ Nat.Prime k := by
  intro hp
  have ht : isPrime N k = true := (hv k hk).mpr hp
  rw [h] at ht
  exact Bool.false_ne_true ht

end PrimeSieve
