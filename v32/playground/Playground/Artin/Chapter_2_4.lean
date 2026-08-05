import Playground.Artin.Chapter_2_3

namespace Artin

def npow {G} [Group G] (g : G) : ℕ → G
  | 0 => 1
  | Nat.succ k => (npow g k) * g

def zpow {G} [Group G] (g : G) : ℤ → G
  | 0 => 1
  | Nat.succ k => npow g (k+1)
  | Int.negSucc k => npow g (k+1)
lemma zpow_of_nat {G} [Group G] (g : G) (n : ℕ) : zpow g (Nat.succ n) = npow g (n + 1) := by rfl

instance {G} [Group G] : Pow G ℕ where
  pow := npow
lemma npow_eq {G} [Group G] (g : G) (z : ℕ) : g^z = npow g z := rfl
@[simp] lemma npow_0 {G} [Group G] (g : G) : g^0 = 1 := by rfl
lemma npow_add_one {G} [Group G] (g : G) (k : ℕ) : g^(k+1) = g^k * g := by rfl

theorem npow_mul_npow {G} [Group G] (g : G) (e₁ e₂ : ℕ) : (g ^ e₁) * g ^ e₂ = g ^ (e₁ + e₂):= by
  induction e₂ with
  | zero => simp
  | succ k IH =>
    rw [npow_eq _ (k+1), npow, ← npow_eq, ← Group.mul_assoc, IH, ← npow_add_one]
    congr 1

instance {G} [Group G] : Pow G ℤ where
  pow := zpow
lemma pow_z_eq_zpow {G} [Group G] (g : G) (z : ℤ) : g^z = zpow g z := rfl
@[simp] lemma zpow_0 {G} [Group G] (g : G) : g^(0 : ℤ) = 1 := by rfl
lemma zpow_add_one {G} [Group G] (g : G) (k : ℤ) : g^(k+1) = g^k * g := by
  rw [pow_z_eq_zpow, pow_z_eq_zpow]
  cases k with
  | ofNat n =>
    rw [show Int.ofNat n = ↑n by rfl]
    rw [zpow_of_nat]
  | negSucc n => sorry



@[simp]
theorem r_zpow (i : ZMod n) (k : ℤ) : (r i) ^ k = r (i * k : ZMod n) := by
  cases k <;> simp [r_pow, neg_mul_eq_mul_neg]

#check DihedralGroup


def cyclicSubgroup {G} [Group G] (g : G) : Subgroup G where
  carrier := { g^k | k : ℤ }
  one_mem := by
    simp only [Set.mem_setOf_eq]
    use 0
    rw [pow_eq, zpow.eq_def]
  mul_mem := by
    intro x y hx hy
    simp at *
    obtain ⟨ e₁, rfl ⟩ := hx
    obtain ⟨ e₂, rfl ⟩ := hy
    use e₁ + e₂
    sorry
  inv_mem := by sorry



end Artin
