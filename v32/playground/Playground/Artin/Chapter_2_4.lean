import Playground.Artin.Chapter_2_3

namespace Artin

variable {G : Type*} [Group G]

@[simp] lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← Group.mul_assoc]; simp

@[simp] lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← Group.mul_assoc]; simp

@[simp] lemma inv_one : (1 : G)⁻¹ = 1 := by
  have h := Group.inv_mul_cancel (1 : G)
  rwa [Group.mul_one] at h

@[simp] lemma inv_inv (a : G) : a⁻¹⁻¹ = a := by
  apply Group.left_cancel a⁻¹
  rw [Group.mul_inv_cancel, Group.inv_mul_cancel]

lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply Group.left_cancel (a * b)
  rw [Group.mul_inv_cancel, Group.mul_assoc]
  simp

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ := by
  have h2 := congr($h * b⁻¹)
  rwa [Group.mul_assoc, Group.mul_inv_cancel, Group.mul_one, Group.one_mul] at h2

private def npow {G} [Group G] (g : G) : ℕ → G
  | 0 => 1
  | k + 1 => (npow g k) * g

instance {G : Type*} [Group G] : Pow G ℕ := ⟨npow⟩

@[simp] lemma pow_zero (g : G) : g ^ 0 = 1 := rfl
@[simp] lemma pow_succ (g : G) (k : ℕ) : g ^ (k + 1) = g ^ k * g := rfl

@[simp] lemma pow_one (g : G) : g ^ 1 = g := by
  have h := pow_succ g 0
  rw [pow_zero, Group.one_mul] at h
  exact h

lemma pow_succ' (g : G) (n : ℕ) : g ^ (n + 1) = g * g ^ n := by
  induction n with
  | zero => simp
  | succ k IH => conv_lhs => rw [pow_succ, IH, Group.mul_assoc, ← pow_succ]

theorem pow_add (g : G) (m n : ℕ) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero => simp
  | succ k IH => rw [← Nat.add_assoc, pow_succ, pow_succ, IH, Group.mul_assoc]

def zpow (g : G) : ℤ → G
  | Int.ofNat n => g ^ n
  | Int.negSucc n => (g ^ (n + 1))⁻¹

instance : Pow G ℤ := ⟨zpow⟩

@[simp] lemma zpow_ofNat (g : G) (n : ℕ) : g ^ (Int.ofNat n) = g ^ n := rfl
@[simp] lemma zpow_natCast (g : G) (n : ℕ) : g ^ (n : ℤ) = g ^ n := rfl
@[simp] lemma zpow_negSucc (g : G) (n : ℕ) : g ^ (Int.negSucc n) = (g ^ (n + 1))⁻¹ := rfl
@[simp] lemma zpow_zero (g : G) : g ^ (0 : ℤ) = 1 := rfl

lemma zpow_add_one (g : G) : ∀ k : ℤ, g ^ (k + 1) = g ^ k * g
  | Int.ofNat n => by
      rw [show (Int.ofNat n + 1 : ℤ) = Int.ofNat (n + 1) from rfl,
          zpow_ofNat, zpow_ofNat, pow_succ]
  | Int.negSucc 0 => by
      rw [show (Int.negSucc 0 + 1 : ℤ) = Int.ofNat 0 from rfl,
          zpow_ofNat, pow_zero, zpow_negSucc, pow_succ, pow_zero,
          Group.one_mul, Group.inv_mul_cancel]
  | Int.negSucc (k + 1) => by
      rw [show (Int.negSucc (k + 1) + 1 : ℤ) = Int.negSucc k from rfl,
          zpow_negSucc, zpow_negSucc, pow_succ' g (k + 1), mul_inv_rev,
          Group.mul_assoc]
      simp

lemma zpow_sub_one (g : G) (k : ℤ) : g ^ (k - 1) = g ^ k * g⁻¹ := by
  have h : g ^ (k - 1) * g = g ^ k := by
    rw [← zpow_add_one]
    congr 1
    omega
  calc g ^ (k - 1) = g ^ (k - 1) * g * g⁻¹ := by
        rw [Group.mul_assoc, Group.mul_inv_cancel, Group.mul_one]
    _ = g ^ k * g⁻¹ := by rw [h]

@[push]
theorem zpow_add (g : G) (m n : ℤ) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k IH =>
      rw [← Int.add_assoc, zpow_add_one, zpow_add_one, IH, Group.mul_assoc]
  | pred k IH =>
      rw [show m + (-(k : ℤ) - 1) = (m + -(k : ℤ)) - 1 by omega,
          zpow_sub_one, zpow_sub_one, IH, Group.mul_assoc]

@[push, push ←] theorem zpow_neg (g : G) (n : ℤ) : g ^ (-n) = (g ^ n)⁻¹ := by
  apply eq_inv_of_mul_eq_one
  rw [← zpow_add, show -n + n = 0 by omega, zpow_zero]

def cyclicSubgroup {G} [Group G] (g : G) : Subgroup G where
  carrier := { g^k | k : ℤ }
  one_mem := by
    simp only [Set.mem_setOf_eq]
    use 0
    simp
  mul_mem := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    obtain ⟨ e₁, rfl ⟩ := hx
    obtain ⟨ e₂, rfl ⟩ := hy
    use e₁ + e₂
    push _ ^ _
    rfl
  inv_mem := by
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
    intro a
    use -a
    exact zpow_neg g a

/- Proposition 2.4.2a - the set of indices k such that x^k=1 -/
def annihilatingIndices (g : G) : AddSubgroup ℤ where
  carrier := { k | g ^ k = 1 }
  zero_mem := by
    simp
  add_mem := by
    simp only [Set.mem_setOf_eq]
    intro x y hx hy
    push _ ^ _
    simp_all
  neg_mem := by
    simp only [Set.mem_setOf_eq]
    intro x h
    push _ ^ _
    simp [h]

@[simp] lemma mem_annihilatingIndices_iff (x : G) (k : ℤ) : k ∈ (annihilatingIndices x).carrier ↔ x ^ k = 1 := by rfl

/- Proposition 2.4.2b -/
example (x : G) (r s : ℤ) : x^r = x^s ↔ x^(r-s) = 1 := by
  constructor
  · intro h
    have := congr($h * x^(-s))
    nth_rw 2 [show x ^ (-s) = (x ^ s)⁻¹ by push _ ^ _; rfl] at this
    simp only [Group.mul_inv_cancel] at this
    pull _ ^ _ at this
    grind
  · intro h
    have := congr($h*x^s)
    simp only [Group.one_mul] at this
    rw [show r - s = r + (-s) by lia] at this
    push _ ^ _ at this
    rw [Group.mul_assoc] at this
    simp_all

@[push, push ←]
lemma zpow_npow_eq_pow_mul (x : G) (r : ℤ) (s : ℕ) : (x^r)^s = x^(r*s) := by
  induction s with
  | zero => simp
  | succ k IH =>
    rw [pow_succ, IH]
    pull _ ^ _
    grind

lemma zpow_zpow_eq_pow_mul (x : G) (r : ℤ) : ∀ s : ℤ, (x^r)^s = x^(r*s)
  | Int.ofNat n => zpow_npow_eq_pow_mul x r n
  | Int.negSucc n => by
    rw [zpow_negSucc]
    rw [← zpow_natCast]
    pull _ ^ _
    norm_cast
    simp only [zpow_negSucc, pow_succ]
    rw [show Int.negSucc n = -(n + 1) by omega]
    rw [show  x ^ (r * -(↑n + 1)) = x^(-(r * (↑n + 1))) by grind]
    rw [zpow_neg]
    congr
    rw [zpow_npow_eq_pow_mul]
    pull _ ^ _
    grind

/- Proposition 2.4.3 - the order of an element -/
noncomputable def order (x : G) : ℕ := generator (annihilatingIndices x)

lemma zpow_order_eq_one (x : G) (r : ℤ) : (x^r)^(order x) = 1 := by
  rw [order]
  rw [zpow_npow_eq_pow_mul]
  rw [← mem_annihilatingIndices_iff]
  grind [multiples_closed, generator_mem]

@[simp] lemma zpow_order_eq_one' (x : G) : x^(order x) = 1 := by
  have := zpow_order_eq_one x 1
  rw [show (1 : ℤ) = Int.ofNat 1 by rfl] at this
  rw [zpow_ofNat] at this
  simp_all

@[simp] lemma one_npow (n : ℕ) : (1 : G)^n = 1 := by
  induction n with
  | zero => simp
  | succ k IH => rw [pow_succ, IH, Group.one_mul]

@[simp] lemma one_zpow : ∀ q : ℤ, (1 : G)^q = 1
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp [zpow_negSucc]

/- The powers x^0, x^1, ..., x^(n-1) -/
def powers (x : G) : Set G := (fun k => x ^ k) '' Set.Ico (0 : ℤ) (order x)

lemma mem_powers_iff (x : G) (k : ℤ) : x ^ k ∈ powers x ↔ (∃ k, (0 ≤ k ∧ k < ↑(order x)) ∧ x ^ k = x ^ k) := by
  unfold powers
  simp

example (x : G) (h : 0 < order x) : (cyclicSubgroup x).carrier ⊆ powers x := by
  intro gn hgn
  obtain ⟨ k, hk, rfl ⟩ := hgn
  obtain ⟨ q, r, rfl, h2 ⟩ := exists_quotient_remainder k (order x) (by positivity)
  push _ ^ _
  rw [← zpow_zpow_eq_pow_mul]
  simp
  sorry


end Artin
