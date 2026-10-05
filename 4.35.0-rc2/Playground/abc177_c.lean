import Std
import Batteries

/-
Given a list A, find the sum A[i]*A[j] over all pairs i < j
-/

def MODULUS := (10^9 + 7)

instance : AlternativeMonad List where
  pure a := [a]
  bind xs f := xs.flatMap f
  failure := []
  orElse xs ys := xs ++ ys ()

-- A spec
def ansSpec (A : Array Int) : Int :=
  let indices := List.finRange A.size
  let pairs := (indices.product indices).filter (fun p => p.1 < p.2)
  let terms := pairs.map (fun p => A[p.1] * A[p.2])
  terms.sum % MODULUS

-- A spec in a more "list comprehension" style
def ansSpec' (A : Array Int) : Int :=
  (do
    let i ← List.finRange A.size
    let j ← List.finRange A.size
    if i < j then
      return A[i] * A[j]
    else
      failure).sum % MODULUS

-- O(n²) algorithm, local mutability
def ans1 (A : Array Int) : Int := Id.run do
  let mut total : Int := 0

  for hi : i in [0:A.size] do
    for hj : j in [i + 1:A.size] do
      total := (total + A[i] * A[j]) % MODULUS

  return total

-- O(n²) algorithm, global mutability
def ans1' (A : Array Int) : Int :=
  let accumulatePairs : StateM Int Unit := do
    for hi : i in [0:A.size] do
      for hj : j in [i + 1:A.size] do
          let total ← get
          set (total + A[i] * A[j])
  let (_, total) := (accumulatePairs).run 0
  total % MODULUS

-- O(n²) algorithm, functional
-- This is kind of useless as it's less clear than the spec or mutable version.
-- The primary advantage is that can easily be ported to functional languages.
def ans2 (A : Array Int) : Int :=
  let modulus := 10^9 + 7
  let rec pairSum : List Int → Int
    | [] => 0
    | x :: xs =>
        xs.foldl (fun total y => total + x * y) 0
          + pairSum xs
  pairSum A.toList % modulus

-- O(n) "divide by 2", functional
def ans3 (A : Array Int) : Int :=
  let total := A.sum
  let term := A.map (fun a => a * a)
  let ret := total^2 - term.sum
  (ret * 500000004) % MODULUS

-- cofactor loop, functional
def ans4 (A : Array Int) : Int :=
  let initial : Int × Int := (0, A.foldl (· + ·) 0)

  let (ret, _) := A.foldl
    (fun (ret, cofactor) a =>
      let cofactor := cofactor - a
      (ret + a * cofactor, cofactor))
    initial

  ret % MODULUS

-- cofactor loop, local mut
def ans5 (A : Array Int) : Int := Id.run do
  let mut ret : Int := 0
  let mut cofactor := A.sum

  for a in A do
    cofactor := cofactor - a
    ret := ret + a * cofactor

  return ret % MODULUS

structure CofactorState where
  ret : Int
  cofactor : Int

def ans2StateM (A : Array Int) : Int :=
  let computation : StateM CofactorState Int := do
    for a in A do
      modify fun s => { s with cofactor := s.cofactor - a }
      modify fun s => { s with ret := s.ret + a * s.cofactor }

    return (← get).ret % MODULUS

  computation.run' {
    ret := 0
    cofactor := A.foldl (· + ·) 0
  }

private theorem filterMapPairs (xs : List α) (p : α → Bool) (f : α → β) :
    (xs.filter p).map f = xs.flatMap (fun a => if p a then [f a] else []) := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases h : p a <;> simp [h, ih]

private theorem spec_eq_comprehension (A : Array Int) : ansSpec A = ansSpec' A := by
  unfold ansSpec ansSpec'
  change _ = ((List.finRange A.size).flatMap fun i =>
    (List.finRange A.size).flatMap fun j => if i < j then [A[i] * A[j]] else []).sum % MODULUS
  simp only [List.product, List.filter_flatMap, List.map_flatMap, List.filter_map,
    filterMapPairs, Function.comp_def]
  simp [apply_ite]

-- A recursive description of the unmodded sum, used only in the proofs.
private def pairSum : List Int → Int
  | [] => 0
  | x :: xs => x * xs.sum + pairSum xs

private def indexedSum (n : Nat) (f : Fin n → Int) : Int :=
  (((List.finRange n).product (List.finRange n)).filter (fun p => p.1 < p.2)).map
    (fun p => f p.1 * f p.2) |>.sum

private theorem sum_mul (x : Int) (xs : List Int) :
    (xs.map (fun y => x * y)).sum = x * xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, Int.mul_add]

private theorem indexedSum_succ (n : Nat) (f : Fin (n+1) → Int) :
    indexedSum (n+1) f = f 0 * ((List.finRange n).map (fun i => f i.succ)).sum +
      indexedSum n (fun i => f i.succ) := by
  simp [indexedSum, List.product, List.finRange_succ, List.filter_flatMap,
    List.filter_map, List.map_flatMap, List.map_map, Function.comp_def,
    List.flatMap_map]
  rw [List.filter_eq_self.mpr (by simp)]
  congr 1
  simpa only [List.map_map, Function.comp_def] using sum_mul (f 0) ((List.finRange n).map (fun i => f i.succ))

private theorem indexedSum_eq_pairSum (xs : List Int) :
    indexedSum xs.length (fun i => xs[i]) = pairSum xs := by
  induction xs with
  | nil => simp [indexedSum, List.product, pairSum]
  | cons x xs ih =>
    simp only [List.length_cons]
    rw [indexedSum_succ]
    simpa [pairSum, List.map_getElem_finRange] using congrArg (fun s => x * xs.sum + s) ih

private theorem spec_eq_pairSum (A : Array Int) :
    ansSpec A = pairSum A.toList % MODULUS := by
  have h := indexedSum_eq_pairSum A.toList
  simpa [indexedSum, ansSpec] using congrArg (fun s => s % (MODULUS : Int)) h

private theorem fold_mul (xs : List Int) (x acc : Int) :
    xs.foldl (fun s y => s + x * y) acc = acc + x * xs.sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih => simp [ih]; grind

private theorem ans2_pairSum (xs : List Int) : ans2.pairSum xs = pairSum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ans2.pairSum, pairSum, fold_mul, ih]

private theorem spec_eq_ans2 (A : Array Int) : ansSpec A = ans2 A := by
  simp [spec_eq_pairSum, ans2, ans2_pairSum, MODULUS]

-- Expanding the square counts each distinct pair twice.
private theorem square_sum (xs : List Int) :
    xs.sum ^ 2 - (xs.map (fun x => x*x)).sum = 2 * pairSum xs := by
  induction xs with
  | nil => simp [pairSum]
  | cons x xs ih => simp only [List.sum_cons, List.map_cons, pairSum]; grind

private theorem spec_eq_ans3 (A : Array Int) : ansSpec A = ans3 A := by
  rw [spec_eq_pairSum]
  have h := square_sum A.toList
  simp only [ans3, ← Array.sum_toList, Array.toList_map]
  rw [h]
  unfold MODULUS
  omega

-- The remaining cofactor is the sum of the unprocessed suffix.
private theorem cofactor_fold (xs : List Int) (acc : Int) :
    xs.foldl (fun (ret, cofactor) a =>
      (ret + a * (cofactor - a), cofactor - a)) (acc, xs.sum) =
        (acc + pairSum xs, 0) := by
  induction xs generalizing acc with
  | nil => simp [pairSum]
  | cons x xs ih =>
    simp only [List.sum_cons, List.foldl_cons]
    have h : x + xs.sum - x = xs.sum := by omega
    rw [h, ih]
    simp [pairSum, Int.add_assoc]

private theorem spec_eq_ans4 (A : Array Int) : ansSpec A = ans4 A := by
  rw [spec_eq_pairSum]
  simp only [ans4, ← Array.foldl_toList, ← List.sum_eq_foldl]
  rw [cofactor_fold]
  simp

private theorem ans4_eq_ans5 (A : Array Int) : ans4 A = ans5 A := by
  simp [ans4, ans5, Array.forIn_pure_yield_eq_foldl, Array.sum_eq_foldl]

-- Reducing the accumulator after each addition preserves the final residue.
private theorem fold_mod (xs : List α) (f : α → Int) (acc : Int)
    (h : acc % (MODULUS : Int) = acc) :
    xs.foldl (fun b x => (b + f x) % (MODULUS : Int)) acc =
      (acc + (xs.map f).sum) % (MODULUS : Int) := by
  induction xs generalizing acc with
  | nil => simp [h]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (Int.emod_emod _ _)]
    unfold MODULUS at *
    omega

-- Invariant for the nested loop over a suffix of the index range.
private theorem nested_range (f : Nat → Int) (n s : Nat) (acc : Int)
    (h : acc % (MODULUS : Int) = acc) :
    (List.range' s n).foldl (fun b i =>
      (List.range' (i+1) (s+n-(i+1))).foldl
        (fun b j => (b + f i * f j) % (MODULUS : Int)) b) acc =
      (acc + pairSum ((List.range' s n).map f)) % (MODULUS : Int) := by
  induction n generalizing s acc with
  | zero => simp [pairSum, h]
  | succ n ih =>
    simp only [List.range'_succ, List.foldl_cons, List.map_cons, pairSum]
    have sub : s + (n+1) - (s+1) = n := by omega
    rw [sub, fold_mod _ _ _ h]
    have step := ih (s+1)
      ((acc + ((List.range' (s+1) n).map (fun j => f s * f j)).sum) % (MODULUS : Int))
      (Int.emod_emod _ _)
    simp only [Nat.add_assoc, Nat.add_comm 1 n] at step
    rw [step]
    have mul := sum_mul (f s) ((List.range' (s+1) n).map f)
    simp only [List.map_map, Function.comp_def] at mul
    rw [mul]
    unfold MODULUS
    omega

private theorem range_values (A : Array Int) :
    (List.range' 0 A.size).map (fun i => A[i]!) = A.toList := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < A.size := by simpa using h₂
    simp [hi]

private theorem spec_eq_ans1 (A : Array Int) : ansSpec A = ans1 A := by
  simp [ans1]
  simp only [← getElem!_pos]
  conv =>
    rhs
    arg 1
    ext b x
    rw [List.foldl_attach (f := fun b j => (b + A[x.val]! * A[j]!) % (MODULUS : Int))]
  rw [List.foldl_attach (f := fun b i =>
    (List.range' (i+1) (A.size-(i+1))).foldl
      (fun b j => (b + A[i]! * A[j]!) % (MODULUS : Int)) b)]

  rw [spec_eq_pairSum]
  have h := nested_range (fun i => A[i]!) A.size 0 0 (by simp)
  simpa [range_values] using h.symm

example (A : Array Int) : ansSpec A = ansSpec' A := spec_eq_comprehension A
example (A : Array Int) : ansSpec A = ans1 A := spec_eq_ans1 A
example (A : Array Int) : ansSpec A = ans2 A := spec_eq_ans2 A
example (A : Array Int) : ansSpec A = ans3 A := spec_eq_ans3 A
example (A : Array Int) : ansSpec A = ans4 A := spec_eq_ans4 A
example (A : Array Int) : ansSpec A = ans5 A := by grind [spec_eq_ans4, ans4_eq_ans5]
