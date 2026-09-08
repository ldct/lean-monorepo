import Std

namespace Radix.ABC177C

def pairs : List Nat → Nat
  | [] => 0
  | x :: xs => x * xs.sum + pairs xs

theorem pairs_append_one (xs : List Nat) (x : Nat) :
    pairs (xs ++ [x]) = pairs xs + xs.sum * x := by
  induction xs with
  | nil => simp [pairs]
  | cons y ys ih =>
    simp [pairs, ih, List.sum_append, List.sum_cons,
      Nat.mul_add, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def scanMod (m running answer : Nat) : List Nat → Nat
  | [] => answer % m
  | x :: xs =>
      scanMod m ((running + x) % m) ((answer + running * x) % m) xs

theorem strip_mod (a b c d m : Nat) :
    (a % m + (b % m) * c + d) % m = (a + b * c + d) % m := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem scanMod_spec (xs : List Nat) (m running answer : Nat) :
    scanMod m running answer xs =
      (answer + running * xs.sum + pairs xs) % m := by
  induction xs generalizing running answer with
  | nil => simp [scanMod, pairs]
  | cons x xs ih =>
    rw [scanMod, ih, strip_mod]
    simp [pairs, List.sum_cons, Nat.mul_add, Nat.add_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem scanMod_correct (xs : List Nat) (m : Nat) :
    scanMod m 0 0 xs = pairs xs % m := by
  simpa using scanMod_spec xs m 0 0

end Radix.ABC177C

namespace Radix.ABC177C

/-- The inner reference loop, accumulating one new column of pairs. -/
def columnMod (m x answer : Nat) : List Nat → Nat
  | [] => answer
  | y :: ys => columnMod m x ((answer + y * x) % m) ys

theorem columnMod_spec (ys : List Nat) (m x answer : Nat)
    (ha : answer < m) :
    columnMod m x answer ys = (answer + ys.sum * x) % m := by
  induction ys generalizing answer with
  | nil => simp [columnMod, Nat.mod_eq_of_lt ha]
  | cons y ys ih =>
    rw [columnMod, ih _ (Nat.mod_lt _ (by omega))]
    rw [show ∀ a b : Nat, (a % m + b) % m = (a + b) % m from
      fun a b => by simp only [Nat.add_mod, Nat.mod_mod]]
    simp [List.sum_cons, Nat.add_mul, Nat.add_assoc]

/-- The reference outer loop, retaining the already processed pre. -/
def referenceMod (m answer : Nat) (pre : List Nat) : List Nat → Nat
  | [] => answer
  | x :: xs => referenceMod m (columnMod m x answer pre) (pre ++ [x]) xs

theorem referenceMod_spec (xs pre : List Nat) (m answer : Nat)
    (ha : answer < m) :
    referenceMod m answer pre xs =
      (answer + pre.sum * xs.sum + pairs xs) % m := by
  induction xs generalizing pre answer with
  | nil => simp [referenceMod, pairs, Nat.mod_eq_of_lt ha]
  | cons x xs ih =>
    rw [referenceMod, columnMod_spec _ _ _ _ ha,
      ih _ _ (Nat.mod_lt _ (by omega))]
    rw [show ∀ a b c : Nat, (a % m + b + c) % m = (a + b + c) % m from
      fun a b c => by simp only [Nat.add_mod, Nat.mod_mod]]
    simp [pairs, List.sum_append, List.sum_cons, Nat.mul_add, Nat.add_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]

theorem referenceMod_correct (xs : List Nat) (m : Nat) (hm : 0 < m) :
    referenceMod m 0 [] xs = pairs xs % m := by
  simpa using referenceMod_spec xs [] m 0 hm

theorem reference_scan_agree (xs : List Nat) (m : Nat) (hm : 0 < m) :
    referenceMod m 0 [] xs = scanMod m 0 0 xs := by
  rw [referenceMod_correct xs m hm, scanMod_correct]

/-- Validated operands keep both multiply-add variants below machine wraparound. -/
theorem multiply_add_bound (answer running x : Nat)
    (ha : answer < 1000000007) (hr : running < 1000000007)
    (hx : x ≤ 1000000000) :
    answer + running * x < 2 ^ 64 := by
  have h := Nat.mul_le_mul (show running ≤ 1000000006 by omega) hx
  omega

theorem uint64_multiply_add_mod (answer running x : UInt64)
    (ha : answer.toNat < 1000000007) (hr : running.toNat < 1000000007)
    (hx : x.toNat ≤ 1000000000) :
    ((answer + running * x) % (1000000007 : UInt64)).toNat =
      (answer.toNat + running.toNat * x.toNat) % 1000000007 := by
  have h := multiply_add_bound answer.toNat running.toNat x.toNat ha hr hx
  have hp : running.toNat * x.toNat < 2 ^ 64 := by omega
  simp only [UInt64.toNat_mod, UInt64.toNat_add, UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt h]
  rfl

theorem uint64_running_mod (running x : UInt64)
    (hr : running.toNat < 1000000007) (hx : x.toNat ≤ 1000000000) :
    ((running + x) % (1000000007 : UInt64)).toNat =
      (running.toNat + x.toNat) % 1000000007 := by
  simp only [UInt64.toNat_mod, UInt64.toNat_add]
  rw [Nat.mod_eq_of_lt (show running.toNat + x.toNat < 2 ^ 64 by omega)]
  rfl

end Radix.ABC177C
