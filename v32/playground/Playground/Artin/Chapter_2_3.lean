import Playground.Artin.Chapter_2_2

namespace Artin

class AddGroup (G : Type*) extends Add G, Zero G, Neg G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
  zero_add : ∀ a : G, 0 + a = a
  add_zero : ∀ a : G, a + 0 = a
  neg_add : ∀ a : G, -a + a = 0
  add_neg : ∀ a : G, a + -a = 0

attribute [simp] AddGroup.add_assoc AddGroup.zero_add AddGroup.add_zero AddGroup.neg_add AddGroup.add_neg

instance : AddGroup ℤ where
  add_assoc := by
    intros a b c
    simp [Int.add_assoc]
  zero_add := by grind
  add_zero := by grind
  neg_add := by grind
  add_neg := by grind

@[ext]
structure AddSubgroup (G : Type*) [AddGroup G] : Type _ where
  carrier : Set G
  zero_mem : 0 ∈ carrier
  add_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  neg_mem : ∀ x : G, x ∈ carrier → -x ∈ carrier

/- Definition 2.3.3 -/

def MultiplesOf (a : ℕ) : AddSubgroup ℤ where
  carrier := { n | ∃ k : ℤ, n = k * a }
  zero_mem := by simp
  add_mem := by
    rintro x y ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    grind
  neg_mem := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    use -n
    grind

notation "ℤ(" n ")" => MultiplesOf n

@[simp] lemma mem_MultiplesOf_iff (a b : ℕ) : ↑a ∈ ℤ(b).carrier ↔ b ∣ a := by
  constructor
  · rintro h
    rw [MultiplesOf] at h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨ k, hk ⟩ := h
    zify
    rw [hk]
    simp
  · rintro h
    have : ∃ k, a = k * b := exists_eq_mul_left_of_dvd h
    obtain ⟨ k, rfl ⟩ := this
    rw [MultiplesOf]
    simp

@[simp] lemma mem_multiplesOf_self (a : ℕ) : ↑a ∈ ℤ(a).carrier := by simp

@[simp] lemma multiplesOf_inj (a b : ℕ) : (ℤ(a) = ℤ(b)) ↔ (a = b) := by
  constructor
  · intro h
    rw [MultiplesOf, MultiplesOf] at h
    simp only [AddSubgroup.mk.injEq] at h
    have h1 : ↑a ∈ ℤ(b).carrier := by
      have helper : ℤ(a).carrier ⊆ ℤ(b).carrier := le_of_eq_of_le h fun ⦃a⦄ a_1 ↦ a_1
      grw [← helper]
      simp
    have h2 : ↑b ∈ ℤ(a).carrier := by
      have helper : ℤ(b).carrier ⊆ ℤ(a).carrier := by exact le_of_eq_of_le (id (Eq.symm h)) fun ⦃a_1⦄ a ↦ a
      grw [← helper]
      simp
    simp_all only [mem_MultiplesOf_iff]
    exact Nat.dvd_antisymm h2 h1
  · grind

lemma AddGroup.right_cancel {G : Type*} [AddGroup G] (a b d : G) (h : a + d = b + d) : a = b := by
  have := congr($h + -d)
  rw [add_assoc, add_assoc] at this
  simp_all

lemma AddGroup.neg_zero {G : Type*} [AddGroup G] : -(0 : G) = 0 := by
  have h : (-0 : G) + 0 = 0 + 0 := by
    rw [AddGroup.neg_add]
    simp
  have := AddGroup.right_cancel (-0 : G) 0 0 h
  exact this

def AddGroup.bot {G : Type*} [AddGroup G] : AddSubgroup G where
  carrier := {0}
  zero_mem := by simp
  add_mem := by simp
  neg_mem := by
    simp [AddGroup.neg_zero]

@[simp]
theorem mem_bot_iff {G : Type*} [AddGroup G] (i : G) : i ∈ AddGroup.bot.carrier ↔ i = 0 := by
  simp only [AddGroup.bot, Set.mem_singleton_iff]

theorem bot_is_subset (H : AddSubgroup ℤ) (i : ℤ)
: i ∈ AddGroup.bot.carrier → i ∈ H.carrier := by
  rw [mem_bot_iff]
  grind [H.zero_mem]

-- every subgroup of ℤ contains a non-negative integer
theorem exists_nonnegative_integer_in_subgroup (H : AddSubgroup ℤ) : H = AddGroup.bot ∨ ∃ a : ℕ, 0 < a ∧ (a : ℤ) ∈ H.carrier := by
  by_cases h : H = AddGroup.bot
  · left
    exact h
  · right
    have : ∃ a : ℤ, (a ≠ 0 ∧ a ∈ H.carrier) := by
      by_contra h'
      apply h
      push Not at h'
      ext i
      constructor
      · intro hi
        simp
        grind
      · exact bot_is_subset H i
    obtain ⟨a, ha1, ha2⟩ := this
    have : 0 < a ∨ a < 0 := by grind
    obtain h | h := this
    · lift a to ℕ using (by grind)
      use a
      grind
    · refine ⟨(-a).toNat, by grind, by grind [H.neg_mem a ha2]⟩

def positiveElements (H : AddSubgroup ℤ) : Set ℕ := { a | 0 < a ∧ (a : ℤ) ∈ H.carrier }

lemma positiveElements_le (H : AddSubgroup ℤ) : (i : ℕ) ∈ positiveElements H → ↑i ∈ H.carrier := by
  intro hi
  simp [positiveElements] at hi
  grind

-- TODO: need k*z notation for AddSubgroup G
lemma multiples_nat_closed (H : AddSubgroup ℤ) (k : ℕ) (z : ℤ) (h : z ∈ H.carrier) : k*z ∈ H.carrier := by
  induction k
  case zero => simp [H.zero_mem]
  case succ n IH =>
    rw [show  ↑(n + 1) * z = n * z + z by grind]
    apply H.add_mem <;> assumption

lemma multiples_closed {H : AddSubgroup ℤ} (k z : ℤ) (h : z ∈ H.carrier) : k*z ∈ H.carrier := by
  induction k
  case zero => simp [H.zero_mem]
  case succ n IH =>
    rw [show (↑n + 1) * z = n * z + z by grind]
    apply H.add_mem <;> assumption
  case pred n IH =>
    rw [show (-↑n - 1) * z = (-n * z) + (-z) by grind]
    apply H.add_mem
    · assumption
    grind [H.neg_mem]

theorem exists_quotient_remainder (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    ∃ (q : ℤ) (r : ℕ), n = d * q + r ∧ r < d := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  refine ⟨n / d, (n % d).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg n hd'.ne')]
    exact Eq.symm (Int.mul_ediv_add_emod n ↑d)
  · rw [← Nat.cast_lt (α := ℤ),
        Int.toNat_of_nonneg (Int.emod_nonneg n hd'.ne')]
    exact Int.emod_lt_of_pos n hd'

/- Theorem 2.3.3 -/
theorem subgroup_is_multiple_of (S : AddSubgroup ℤ) : ∃ a : ℕ, S = ℤ(a) := by
  have : S = AddGroup.bot ∨ S ≠ AddGroup.bot := by grind
  obtain rfl | h := this
  · use 0
    ext i
    simp [MultiplesOf]
  · let a := sInf (positiveElements S)
    use a
    have hnonempty : Set.Nonempty (positiveElements S) := by
      have := exists_nonnegative_integer_in_subgroup S
      simp only [h, false_or] at this
      obtain ⟨a, ha⟩ := this
      use a
      simp_all [positiveElements]
    have ha_minimal : ∀ χ ∈ (positiveElements S), a ≤ χ := fun y hn => by
      rw [← show sInf (positiveElements S) = a by rfl]
      apply Nat.sInf_le
      exact hn
    obtain ⟨ ha1, ha2⟩ := show 0 < a ∧ ↑a ∈ S.carrier by
      have := Nat.sInf_mem hnonempty
      rw [show sInf (positiveElements S) = a by rfl] at this
      simp [positiveElements] at this
      assumption
    · ext n
      constructor
      · -- next we show that S is a subset of ℤa, ...
        intro hn
        obtain ⟨ q, r, h1, h2 ⟩ := exists_quotient_remainder n a (by grind)
        have : r = n + (-q) * a := by grind
        have : (r : ℤ) ∈ S.carrier := by
          rw [this]
          apply S.add_mem
          · exact hn
          apply multiples_closed
          exact ha2
        have : r = 0 := by
          by_contra hr
          specialize ha_minimal r (by
            simp [positiveElements]
            grind
          )
          grind
        subst this
        have : n = q * a := by grind
        rw [this]
        apply multiples_closed
        exact mem_multiplesOf_self _
      · -- we first show that ℤa is a subset of S, ...
        intro hn
        simp only [MultiplesOf, Set.mem_setOf_eq] at hn
        obtain ⟨k, rfl⟩ := hn
        apply multiples_closed
        grind [positiveElements_le]

/- For a subgroup S of ℤ, the generator is unique nonnegative integer such that S = ℤ(generator S). -/
noncomputable def generator (S : AddSubgroup ℤ) : ℕ := (subgroup_is_multiple_of S).choose

lemma generator_spec (S : AddSubgroup ℤ) : S = ℤ(generator S) := (subgroup_is_multiple_of S).choose_spec

lemma generator_eq_iff (S : AddSubgroup ℤ) (a : ℕ) : generator S = a ↔ S = ℤ(a) := by
  grind [multiplesOf_inj, generator_spec]

lemma generator_mem (S : AddSubgroup ℤ) : ↑(generator S) ∈ S.carrier := by
  grind [mem_multiplesOf_self, generator_spec]

/- Definition 2.3.3 -/
def Sum (a b : ℤ) : AddSubgroup ℤ where
  carrier := { n | ∃ r s : ℤ, n = r * a + s * b }
  zero_mem := by
    simp only [Set.mem_setOf_eq]
    use 0, 0
    grind
  add_mem := by
    rintro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    obtain ⟨r, s, rfl⟩ := hx
    obtain ⟨t, u, rfl⟩ := hy
    use r + t, s + u
    grind
  neg_mem := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    obtain ⟨p, q, rfl⟩ := hx
    use -p, -q
    grind

lemma mem_sum_iff (a b : ℤ) (n : ℤ) : (n ∈ (Sum a b).carrier) ↔ (∃ r s : ℤ, n = r * a + s * b) := by
  rfl

lemma sum_symm (a b : ℤ) : Sum a b = Sum b a := by
  ext n
  simp only [mem_sum_iff]
  constructor
  · rintro ⟨r, s, rfl⟩
    use s, r
    grind
  · rintro ⟨r, s, rfl⟩
    use s, r
    grind

-- Definition: gcd(a, b) is the (unique) d for which ℤd = ℤa + ℤb
noncomputable def gcd (a b : ℤ) : ℕ := generator (Sum a b)

@[simp] lemma sum_eq (a b : ℤ) : Sum a b = ℤ(gcd a b) := by grind [gcd, generator_spec]

lemma gcd_symm (a b : ℤ) : gcd a b = gcd b a := by grind [gcd, sum_eq, sum_symm]

/- Proposition 2.3.5 -/

lemma part_c (a b : ℤ) : ∃ r s : ℤ, gcd a b = r * a + s * b := by
  have h1 := generator_spec (Sum a b)
  have h2 := mem_multiplesOf_self (generator (Sum a b))
  rw [← h1] at h2
  rw [mem_sum_iff] at h2
  exact h2

lemma mem_multipleOf_iff (a : ℤ) (b : ℕ) : ↑a ∈ ℤ(b).carrier ↔ ∃ k : ℤ, a = k * b := by rfl

lemma part_a (a b : ℤ) : ↑(gcd a b) ∣ a := by
  have a_mem : a ∈ (Sum a b).carrier := by
    rw [mem_sum_iff]
    use 1, 0
    norm_num
  simp only [sum_eq] at a_mem
  rw [mem_multipleOf_iff] at a_mem
  obtain ⟨ k, hk ⟩ := a_mem
  nth_rw 2 [hk]
  simp

lemma part_a' (a b : ℤ) : ↑(gcd a b) ∣ b := by
  grind [gcd_symm, part_a]

lemma part_b (e a b : ℤ) (h1 : e ∣ a) (h2 : e ∣ b) : e ∣ gcd a b := by
  have := part_c a b
  obtain ⟨ r, s, gcd_eq ⟩ := this
  rw [gcd_eq]
  exact Dvd.dvd.linear_comb h1 h2 r s

/- Euclidean algorithm -/

lemma sum_diff (a b : ℤ) : Sum a b = Sum (a - b) b := by
  ext x
  constructor
  · rintro ⟨ r, s, rfl ⟩
    rw [mem_sum_iff]
    use r, r+s
    grind
  · rintro ⟨ r, s, rfl ⟩
    rw [mem_sum_iff]
    use r, s-r
    grind


lemma gcd_diff (a b : ℤ) : gcd a b = gcd (a - b) b := by
  have := sum_diff a b
  simp_all

lemma sum_0 (a : ℤ) : Sum a 0 = ℤ(a.natAbs) := by
  rw [Sum, MultiplesOf]
  suffices _ : {n | ∃ r, n = r * a} = {n | ∃ k, n = k * |a|} by
    simp_all
  ext i
  simp only [Set.mem_setOf_eq] at *
  constructor
  · rintro ⟨ r, rfl ⟩
    use r * a.sign, by grind [Int.sign_mul_abs]
  · rintro ⟨ k, rfl ⟩
    use k * a.sign, by grind [Int.sign_mul_abs]

lemma gcd_0 (a : ℤ) : gcd a 0 = a.natAbs := by
  grind [gcd, sum_0, generator_eq_iff]

example : gcd 314 136 = 2 := by
  calc _ = gcd 178 136 := gcd_diff _ _
       _ = gcd 42  136 := gcd_diff _ _
       _ = gcd 136 42 := gcd_symm _ _
       _ = gcd 94  42 := gcd_diff _ _
       _ = gcd 52  42 := gcd_diff _ _
       _ = gcd 10  42 := gcd_diff _ _
       _ = gcd 42  10 := gcd_symm _ _
       _ = gcd 32  10 := gcd_diff _ _
       _ = gcd 22  10 := gcd_diff _ _
       _ = gcd 12  10 := gcd_diff _ _
       _ = gcd 2   10 := gcd_diff _ _
       _ = gcd 10  2 := gcd_symm _ _
       _ = gcd 8   2 := gcd_diff _ _
       _ = gcd 6   2 := gcd_diff _ _
       _ = gcd 4   2 := gcd_diff _ _
       _ = gcd 2   2 := gcd_diff _ _
       _ = gcd 0   2 := gcd_diff _ _
       _ = gcd 2   0 := gcd_symm _ _
       _ = _ := gcd_0 _



end Artin
