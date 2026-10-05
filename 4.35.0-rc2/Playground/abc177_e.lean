import Std
import Batteries

/-
Given a list of integers A, determine if it is pairwise copirme
-/

instance : AlternativeMonad List where
  pure a := [a]
  bind xs f := xs.flatMap f
  failure := []
  orElse xs ys := xs ++ ys ()

def ansSpec (A : Array Nat) : Bool :=
  let indices := List.finRange A.size
  let pairs := (indices.product indices).filter (fun p => p.1 < p.2)
  ∀ p ∈ pairs, (Nat.gcd A[p.1] A[p.2] = 1)

-- A spec in a more "list comprehension" style
def ansSpec' (A : Array Nat) : Bool :=
  (do
    let i ← List.finRange A.size
    let j ← List.finRange A.size
    if i < j then
      return decide (1 = Nat.gcd A[i] A[j])
    else
      failure).all (fun x => x)

-- O(n²) algorithm, local mutability
def ans1 (A : Array Nat) : Bool := Id.run do
  for hi : i in [0:A.size] do
    for hj : j in [i + 1:A.size] do
      if 1 != Nat.gcd A[i] A[j] then
        return false

  return true

def Nat.IsPrime (n : Nat) : Bool := Id.run do
  if n < 2 then
    return false
  for d in [2:n.sqrt + 1] do
    if n % d == 0 then
      return false
  return true

def primesUpTo (n : Nat) : Array Nat :=
  let r₁ := List.finRange (n+1)
  let r₂ := r₁.map (fun x => x.val)
  let r₃ := r₂.filter (fun x => x.IsPrime)
  r₃.toArray


-- trial division loop, local mut
def ans5 (A : Array Nat) : Bool := Id.run do
  let primes := primesUpTo (A.max?.getD 0).sqrt
  let mut seen : Std.HashSet Nat := ∅

  for x in A do
    let mut x' := x
    for p in primes do
      if p * p > x then
        break
      if x % p = 0 then
        if p ∈ seen then
            return false
          seen := seen.insert p
          while p ∣ x' do
            x' := x' / p
    if x' > 1 then
      if x' ∈ seen then
        return false
      seen := seen.insert x'

  return true

theorem ans5_eq_ansSpec
    (A : Array Nat)
    (hpos : ∀ i : Fin A.size, 0 < A[i]) :
    ans5 A = ansSpec A := by
  sorry
