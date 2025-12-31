import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic

/-- Dicyclic group Dicₙ (order 4n) in normal form: a^k or x a^k. -/
inductive DicyclicGroup (n : ℕ) : Type
  | a  : ZMod (2*n) → DicyclicGroup n
  | ax : ZMod (2*n) → DicyclicGroup n
  deriving DecidableEq

namespace DicyclicGroup

variable {n : ℕ}

open DicyclicGroup

def mul : DicyclicGroup n → DicyclicGroup n → DicyclicGroup n
  | a k,  a m  => a (k + m)
  | a k, ax m => ax (k + m)
  | ax k, a m => ax (k - m)
  | ax k, ax m => a (k - m + n)

instance : Mul (DicyclicGroup n) where
  mul := mul

theorem mul_eq (x y : DicyclicGroup n) : x * y = match x, y with
  | a k,  a m  => a (k + m)
  | a k, ax m => ax (k + m)
  | ax k, a m => ax (k - m)
  | ax k, ax m => a (k - m + n)
  := rfl

theorem mul_assoc : ∀ a b c : DicyclicGroup n, (a * b) * c = a * (b * c) := by
  have : (n : ZMod (2*n)) + (n : ZMod (2*n)) = 0 := by
    norm_cast
    rw [show n + n = 2 * n by ring]
    exact ZMod.natCast_self (2 * n)
  rintro (i | i) (j | j) (k | k) <;> simp [mul_eq] <;> grind

def one : DicyclicGroup n := a 0

instance : One (DicyclicGroup n) where
  one := one

def inv : DicyclicGroup n → DicyclicGroup n
  | a k => a (-k)
  | ax k => ax (n+k)

instance : Inv (DicyclicGroup n) where
  inv := inv

theorem inv_eq (g : DicyclicGroup n) : g.inv = match g with
  | a k => a (-k)
  | ax k => ax (n+k)
  := rfl

instance : Group (DicyclicGroup n) := {
  mul_assoc a b c := mul_assoc a b c
  one_mul := by
    rintro (i | i) <;> rw [show (1 : DicyclicGroup n) = DicyclicGroup.a 0 by rfl] <;> simp [mul_eq]
  mul_one := by
    rintro (i | i) <;> rw [show (1 : DicyclicGroup n) = DicyclicGroup.a 0 by rfl] <;> simp [mul_eq]
  inv a := inv a
  inv_mul_cancel := by
    have : (n : ZMod (2*n)) + (n : ZMod (2*n)) = 0 := by
      norm_cast
      rw [show n + n = 2 * n by ring]
      exact ZMod.natCast_self (2 * n)
    rintro (i | i) <;> simp [inv_eq, mul_eq, show (1 : DicyclicGroup n) = DicyclicGroup.a 0 by rfl]
    exact this
}

instance (n : ℕ) [NeZero n] : NeZero (2 * n) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne n)⟩

instance [NeZero n] : Fintype (DicyclicGroup n) where
  elems := (Finset.univ.map ⟨a, by intro x y h; injection h⟩) ∪
           (Finset.univ.map ⟨ax, by intro x y h; injection h⟩)
  complete := by
    intro x
    simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
      Finset.mem_univ, true_and]
    cases x with
    | a k => left; exact ⟨k, rfl⟩
    | ax k => right; exact ⟨k, rfl⟩


theorem center_eq (n : ℕ) (hn : 2 < n) : (Subgroup.center (DicyclicGroup n)).carrier = { 1, a n } := by
  apply Set.ext
  intro x
  simp
  constructor;
  · rcases x with ( _ | _ ) <;> simp_all +decide [ Subsemigroup.mem_center_iff ];
    · rename_i k;
      intro hk; have := hk ( DicyclicGroup.ax 0 ) ; simp_all +decide [ DicyclicGroup.mul_eq ] ;
      -- Since $-k = k$, we have $2k = 0$, which implies $k = 0$ or $k = n$.
      have hk_cases : k = 0 ∨ k = n := by
        have hk_cases : 2 * k = 0 := by
          grind;
        have hk_cases : ∃ m : ℕ, k = m ∧ m < 2 * n ∧ 2 * m ≡ 0 [MOD 2 * n] := by
          use k.val;
          haveI := Fact.mk ( by linarith : 1 < 2 * n )
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
          exact ZMod.val_lt k;
        rcases hk_cases with ⟨ m, rfl, hm₁, hm₂ ⟩
        rcases Nat.dvd_of_mod_eq_zero hm₂ with ⟨ c, hc ⟩
        rcases c with ( _ | _ | c ) <;> simp_all
        nlinarith
      aesop
    · intro h; have := h ( DicyclicGroup.a 1 )
      simp_all +decide [ mul_eq ]
      have h_contra : (2 : ZMod (2 * n)) = 0 := by grind
      rcases n with ( _ | _ | n ) <;> cases h_contra
      contradiction
  · rintro ( rfl | rfl ) <;> simp +decide [ Subsemigroup.mem_center_iff ];
    rintro ( _ | _ ) <;> simp +decide [ mul_eq ];
    · exact add_comm _ _;
    · ring_nf
      rw [ sub_eq_add_neg ]
      norm_num [ ZMod.neg_eq_self_iff ]
      right
      exact Nat.mod_eq_of_lt ( by linarith )

end DicyclicGroup
