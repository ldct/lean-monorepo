import Mathlib

set_option linter.style.longLine false

/-
This file formalizes the definitions, theorems and exercises from Chapter 1.1 of Dummit and Foote (page 16).
-/

class MyGroup (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

class MyAddGroup (G : Type*) extends Add G, Zero G, Neg G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
  zero_add : ∀ a : G, 0 + a = a
  add_zero : ∀ a : G, a + 0 = a
  neg_add_cancel : ∀ a : G, a + (-a) = 0
  add_neg_cancel : ∀ a : G, (-a) + a = 0

instance : MyAddGroup ℚ where
  add_assoc a b c := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_neg_cancel := by grind

instance : MyAddGroup ℝ where
  add_assoc a b c := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_neg_cancel := by grind

instance : MyAddGroup ℂ where
  add_assoc a b c := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_neg_cancel := by grind

/-
Example 6
-/
instance {A B} [MyGroup A] [MyGroup B] : Mul (A × B) := {
  mul := fun a b ↦ (a.1 * b.1, a.2 * b.2)
}

lemma MyGroup.prod_mul {A B} [MyGroup A] [MyGroup B] (a b : A × B) : a * b = (a.1 * b.1, a.2 * b.2) := rfl

instance {A B} [MyGroup A] [MyGroup B] : One (A × B) := {
  one := (1, 1)
}

instance {A B} [MyGroup A] [MyGroup B] : MyGroup (A × B) where
  mul_assoc := by
    rintro ⟨ a₁, a₂ ⟩ ⟨ b₁, b₂ ⟩ ⟨ c₁, c₂ ⟩
    simp [MyGroup.prod_mul]
    constructor
    · exact MyGroup.mul_assoc a₁ b₁ c₁
    · exact MyGroup.mul_assoc a₂ b₂ c₂
  one_mul := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.one_mul]
  mul_one := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.mul_one]
  inv_mul_cancel := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.inv_mul_cancel]
  mul_inv_cancel := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.mul_inv_cancel]

/-
Proposition 1.1

The identity is unique. We formulate this as: there is a unique element `e` such that `IsNeutralElement e` holds.
`∃!x, P x` is syntactic sugar for `∃ x, P x ∧ ∀ y, P y → y = x`.
-/

def MyGroup.IsNeutralElement {G} [MyGroup G] (e : G) : Prop := ∀ a : G, e * a = a ∧ a * e = a

lemma MyGroup.IsNeutralElement.unique {G} [MyGroup G] : ∃! e : G, IsNeutralElement e := by
  use 1
  constructor
  · intro a
    simp [MyGroup.one_mul, MyGroup.mul_one]
  · intro y hy
    have := hy 1
    grind [MyGroup.one_mul]

/-
Proposition 1.2

The inverse is unique. We formulate this as: for every element `a`, we have ∃! b, AreInverse a b
-/

def MyGroup.AreInverse {G} [MyGroup G] (a b : G) : Prop := a * b = 1 ∧ b * a = 1

lemma MyGroup.AreInverse.right_unique {G} [MyGroup G] (a b c : G) (hb : AreInverse a b) (hc : AreInverse a c) : c = b := by
  calc
    c = c * 1 := by simp [MyGroup.mul_one]
    _ = c * (a * b) := by (congr 1; rw [hb.1])
    _ = (c * a) * b := by rw [MyGroup.mul_assoc]
    _ = 1 * b := by (congr 1; rw [hc.2])
    _ = b := by simp [MyGroup.one_mul]

lemma MyGroup.AreInverse.helper {G} [MyGroup G] (a : G) : AreInverse a a⁻¹ := by grind [AreInverse, MyGroup.inv_mul_cancel, MyGroup.mul_inv_cancel]

lemma MyGroup.AreInverse.right_unique_exists {G} [MyGroup G] (a : G) : ∃! b : G, AreInverse a b := by
  use a⁻¹
  have h' := helper a
  grind [right_unique]

lemma MyGroup.AreInverse.iff {G} [MyGroup G] (a b : G) : AreInverse a b ↔ a⁻¹ = b := by
  have h' := helper a
  grind [right_unique]

lemma MyGroup.AreInverse.symm {G} [MyGroup G] (a b : G) : AreInverse a b ↔ AreInverse b a := by grind [MyGroup.AreInverse]

lemma MyGroup.AreInverse.left_unique {G} [MyGroup G] (a b c : G) (hb : AreInverse b a) (hc : AreInverse c a) : b = c := by
  grind [MyGroup.AreInverse.symm, MyGroup.AreInverse.right_unique]

/-
Proposition 1.3
-/

lemma MyGroup.inv_inv {G} [MyGroup G] (a : G) : (a⁻¹)⁻¹ = a := by
  rw [← MyGroup.AreInverse.iff]
  grind [MyGroup.AreInverse.symm, MyGroup.AreInverse.helper]

/-
Proposition 1.4

We use an alternate proof, pulling forward some ideas from Poposition 2.
-/

lemma MyGroup.test2 {G} [MyGroup G] (a b : G) (h : a * b = 1) : (b * a = 1) := by
  have := congrArg (fun x => x * b⁻¹) h
  dsimp at this
  rw [mul_assoc, mul_inv_cancel, mul_one, one_mul] at this
  have := congrArg (fun x => x⁻¹) this
  dsimp at this
  rw [inv_inv] at this
  rw [← AreInverse.iff] at this
  exact this.2

theorem MyGroup.AreInverse.iff' {G} [MyGroup G] (a b : G) : AreInverse a b ↔ a * b = 1 := by
  constructor
  · intro h
    exact h.1
  · intro h
    have := test2 a b h
    grind [AreInverse]

example {G} [MyGroup G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← MyGroup.AreInverse.iff]
  rw [MyGroup.AreInverse.iff']
  rw [← MyGroup.mul_assoc, MyGroup.mul_assoc a b, MyGroup.mul_inv_cancel, MyGroup.mul_one, MyGroup.mul_inv_cancel]

/-
Cancellation laws
-/
lemma MyGroup.mul_left_cancel {G} [MyGroup G] (a u v : G) : a * u = a * v ↔ u = v := by
  constructor
  · intro h
    have := congrArg (fun x => a⁻¹ * x) h
    dsimp at this
    rwa [← MyGroup.mul_assoc, MyGroup.inv_mul_cancel, MyGroup.one_mul, ← MyGroup.mul_assoc, MyGroup.inv_mul_cancel, MyGroup.one_mul] at this
  · grind

lemma MyGroup.mul_right_cancel {G} [MyGroup G] (b u v : G) : u * b = v * b ↔ u = v := by
  constructor
  · intro h
    have := congrArg (fun x => x * b⁻¹) h
    dsimp at this
    rwa [MyGroup.mul_assoc, MyGroup.mul_inv_cancel, MyGroup.mul_one, MyGroup.mul_assoc, MyGroup.mul_inv_cancel, MyGroup.mul_one] at this
  · grind

/-
Exponentiation
-/
def MyGroup.npow {G} [MyGroup G] (g : G) (n : ℕ) : G :=
  match n with
  | 0 => 1
  | n + 1 => g * npow g n

instance {G} [MyGroup G] : Pow G ℕ := {
  pow := MyGroup.npow
}

lemma MyGroup.npow_zero {G} [MyGroup G] (g : G) : g ^ 0 = 1 := rfl

lemma MyGroup.npow_succ {G} [MyGroup G] (g : G) (n : ℕ) : g ^ (n + 1) = g * g ^ n := rfl

lemma MyGroup.npow_add {G} [MyGroup G] (g : G) (m n : ℕ) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero =>
    simp [MyGroup.npow_zero];
    -- By definition of exponentiation in the group, we know that $g^m * 1 = g^m$.
    apply Eq.symm; exact (by
      have := (‹MyGroup G›).mul_one g;
      convert ( ‹MyGroup G›.mul_one _ ) using 1
    )
  | succ n IH =>
    simp_all [ ← add_assoc, MyGroup.npow_succ ]
    induction' m with m IH generalizing n;
    · simp [ ← mul_assoc, MyGroup.npow_zero ]
      simp [ MyGroup.mul_one, MyGroup.one_mul ]
    · simp_all [ ← mul_assoc ]
      apply_assumption
      ext; simp [ mul_assoc ]
      induction' m + 1 with m IH <;> simp_all [ ← mul_assoc ];
      · simp [MyGroup.npow_zero]
        simp [ MyGroup.mul_one, MyGroup.one_mul ]
      · simp_all [ MyGroup.npow_succ, mul_assoc ]

def MyGroup.zpow {G} [MyGroup G] (g : G) (n : ℤ) : G :=
  match n with
  | Int.ofNat n => g ^ n
  | Int.negSucc n => (g ^ (n + 1))⁻¹

instance {G} [MyGroup G] : Pow G ℤ := {
  pow := MyGroup.zpow
}

lemma MyGroup.zpow_cast {G} [MyGroup G] (g : G) (n : ℕ) : g ^ (n : ℤ) = g ^ (n : ℕ) := by
  rfl

/-
https://proofwiki.org/wiki/Index_Laws_for_Monoids/Sum_of_Indices very long and requires monoid homomorphisms

Dummit and Foote just assume it implicitly
-/
lemma MyGroup.zpow_add {G} [MyGroup G] (g : G) (m n : ℤ) : g ^ (m + n) = g ^ m * g ^ n := by
  cases m with
  | ofNat m =>
    cases n with
    | ofNat n =>
      simp [zpow_cast]
      norm_cast
      rw [zpow_cast g (m + n)]
      rw [npow_add]
    | negSucc n =>
      simp

lemma MyGroup.zpow_zero {G} [MyGroup G] (g : G) : g ^ (0 : ℤ) = 1 := by
  rfl

lemma MyGroup.zpow_neg {G} [MyGroup G] (g : G) (n : ℤ) : g ^ (-n) = (g ^ n)⁻¹ := by
  rcases n with ⟨ _ | n ⟩ <;> norm_cast;
  · cases' ‹MyGroup G› with G hG;
    rename_i h₁ h₂ h₃ h₄ h₅;
    exact Eq.symm ( by have := h₄ 1; have := h₅ 1; aesop );
  · erw [ eq_comm ];
    cases' ‹MyGroup G› with G_mul G_one G_inv G_mul_assoc G_one_mul G_mul_one G_inv_mul_cancel G_mul_inv_cancel;
    have h_inv : ∀ a : G, (a⁻¹)⁻¹ = a := by
      intro a; exact (by
      have := G_mul_assoc a⁻¹⁻¹ a⁻¹ a;
      grind);
    aesop

lemma MyGroup.zpow_mul_nat {G} [MyGroup G] (g : G) (m : ℤ) (n : ℕ) : g ^ (m * (n : ℤ)) = (g ^ m) ^ (n : ℤ) := by
  induction' n with n ih generalizing m <;> simp_all +decide [ pow_add, pow_mul ];
  · exact?;
  · simp +decide [ zpow_add, zpow_mul, mul_add, add_comm, add_left_comm, ih ];
    simp +decide [ ← mul_assoc, ← zpow_add, add_comm ];
    exact?

lemma MyGroup.zpow_mul {G} [MyGroup G] (g : G) (m n : ℤ) : g ^ (m * n) = (g ^ m) ^ n := by
  -- We proceed by cases on `n`. Since `n` can be either non-negative or negative, we split into these two cases.
  by_cases hn : 0 ≤ n;
  · cases n <;> simp_all +decide [ zpow_mul_nat ];
  · -- Since `n` is negative, we can write `n = -k` for some `k : ℕ`.
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k := by
      exact ⟨ Int.toNat ( -n ), by rw [ Int.toNat_of_nonneg ( neg_nonneg.mpr ( le_of_not_ge hn ) ) ] ; ring ⟩;
    simp +decide [ *, zpow_neg, zpow_mul_nat ]

noncomputable section AristotleLemmas

lemma MyGroup.zpow_mul_zpow_neg {G} [MyGroup G] (g : G) (n : ℤ) : g ^ n * g ^ (-n) = 1 := by
  have := @MyGroup.zpow_add G ‹_› g n ( -n );
  rw [ ← this, add_neg_cancel ];
  exact?

end AristotleLemmas

lemma MyGroup.zpow_inv {G} [MyGroup G] (g : G) (n : ℤ) : g ^ (-n) = (g ^ n)⁻¹ := by
  have := @MyGroup.zpow_mul_zpow_neg;
  specialize @this G ‹_› g n;
  have := @MyGroup.mul_inv_cancel;
  specialize @this G ‹_›;
  have := @MyGroup.mul_left_cancel G ‹_›;
  grind

lemma MyGroup.zpow_pow {G} [MyGroup G] (g : G) (m n : ℤ) : g ^ (m * n) = (g ^ m) ^ n := by
  -- By commutativity of multiplication, we have $n * m = m * n$.
  have h_comm : n * m = m * n := by
    -- By commutativity of multiplication, we have $n * m = m * n$ for any integers $n$ and $m$.
    apply mul_comm;
  -- By the associativity of multiplication, we have $m * n = n * m$.
  apply Eq.symm; exact (by
  -- Apply the lemma MyGroup.zpow_mul which states that for any integers m and n, g^(m*n) = (g^m)^n. This follows directly from the properties of exponents in a group.
  apply Eq.symm; exact (by
    have := @MyGroup.zpow_mul G ‹_› g m n;
    exact this))

noncomputable section AristotleLemmas

/-
The inverse of a product is the product of the inverses in reverse order.
-/
lemma MyGroup.mul_inv_rev {G} [MyGroup G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have := ‹MyGroup G›;
  rename_i h;
  revert this;
  cases' h with h1 h2;
  rename_i h3 h4 h5 h6 h7 h8;
  exact fun h => by
    -- By multiplying both sides of the equation $a * b * (a * b)⁻¹ = 1$ by $a⁻¹$ on the left, we get $b * (a * b)⁻¹ = a⁻¹$.
    have h_mul_a_inv : b * (a * b)⁻¹ = a⁻¹ := by
      have h_mul_a_inv : a⁻¹ * (a * b * (a * b)⁻¹) = a⁻¹ * 1 := by
        exact?;
      grind;
    rw [ ← h_mul_a_inv, ← h4 ];
    rw [ h7, h5 ]

/-
The inverse of the n-th power is the n-th power of the inverse.
-/
lemma MyGroup.inv_npow {G} [MyGroup G] (g : G) (n : ℕ) : (g⁻¹) ^ n = (g ^ n)⁻¹ := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n );
  · cases' ‹MyGroup G› with _ _ _ _ _ h;
    rename_i h₁ h₂ h₃;
    have := h₂ ( g * g⁻¹ ) ; simp_all +decide [ mul_assoc ] ;
    exact?;
  · simp +decide [ MyGroup.npow_succ ];
    simp +decide [ MyGroup.npow_zero ];
    simp +decide [ MyGroup.mul_one ];
  · simp_all +decide [ MyGroup.npow_succ, MyGroup.mul_assoc, MyGroup.mul_inv_rev ];
    simp +decide [ ← mul_assoc, ← ih n ( Nat.lt_succ_of_lt ( Nat.lt_succ_self _ ) ) ];
    induction' n with n ih;
    · simp +decide [ MyGroup.npow_zero ];
      simp +decide [ MyGroup.mul_one, MyGroup.one_mul ];
    · simp_all +decide [ ← mul_assoc, ← ih ];
      induction' n + 1 with n ih <;> simp_all +decide [ pow_succ', mul_assoc ];
      · simp +decide [ MyGroup.npow_zero ];
        simp +decide [ MyGroup.one_mul ];
      · simp_all +decide [ ← mul_assoc, MyGroup.npow_succ ]

end AristotleLemmas

lemma MyGroup.inv_zpow {G} [MyGroup G] (g : G) (n : ℤ) : (g⁻¹) ^ n = g ^ (-n) := by
  -- We can prove the `zpow` case in the same way since `zpow` is defined in terms of `npow`.
  by_cases hn : 0 ≤ n;
  · obtain ⟨ k, rfl ⟩ := Int.eq_ofNat_of_zero_le ‹_›;
    simp +decide [ MyGroup.zpow_inv ];
    -- Apply the lemma that states the inverse of the nth power is the nth power of the inverse.
    have := @MyGroup.inv_npow G ‹_› g k;
    aesop;
  · induction' n using Int.negInduction with n ih;
    · grind;
    · simp +decide [ *, MyGroup.zpow_cast, MyGroup.zpow_inv ];
      simp +decide [ *, MyGroup.inv_npow, MyGroup.inv_inv ]
