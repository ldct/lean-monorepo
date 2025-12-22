import Mathlib

def IsGeneratedBy {G} [Group G] (g : G) : Prop :=
  ∀ h : G, ∃ n : ℤ, g ^ n = h

def MyIsCyclic (G) [Group G] : Prop :=
  ∃ g : G, IsGeneratedBy g

theorem isGeneratedBy_inv {G} [Group G] (g : G) (h1 : IsGeneratedBy g)
: IsGeneratedBy g⁻¹ := by
  unfold IsGeneratedBy at *
  intro h
  obtain ⟨ n, hn ⟩ := h1 h
  use -n
  simp [← hn]

-- Comment: a cyclic group may have more than one generator
theorem isGeneratedBy_iff_isGeneratedBy_inv {G} [Group G] (g : G) :
IsGeneratedBy g ↔ IsGeneratedBy g⁻¹ := by
  constructor
  · exact isGeneratedBy_inv g
  · intro h
    have := isGeneratedBy_inv _ h
    simpa

def IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

-- Comment: by the law of exponents, cyclic groups are abelian.
theorem isAbelian_of_myIsCyclic {G} [Group G] (h1 : MyIsCyclic G) : IsAbelian G := by
  unfold IsAbelian MyIsCyclic at *
  intro x y
  obtain ⟨ g, hg ⟩ := h1
  unfold IsGeneratedBy at hg
  obtain ⟨ n, rfl ⟩ := hg x
  obtain ⟨ m, rfl ⟩ := hg y
  group

example (n : ℕ) [Fact (2 < n)] : ¬ MyIsCyclic (DihedralGroup n) := by
  intro h
  have := isAbelian_of_myIsCyclic h
  specialize this (DihedralGroup.r 1) (DihedralGroup.sr 0)
  simp at this
  have t : ((-1 : ZMod n) = 1) -> False := by {
    apply ZMod.neg_one_ne_one
  }
  grind



def GeneratesAdditvely {G} [AddGroup G] (g : G) : Prop :=
  ∀ h : G, ∃ n : ℤ, n • g = h

example : GeneratesAdditvely (1 : ZMod 48) := by
  simp [GeneratesAdditvely]
  intro h
  use h.val
  simp

example : GeneratesAdditvely (-1 : ZMod 48) := by
  simp [GeneratesAdditvely]
  intro h
  use (-h.val)
  simp

example : ¬ (GeneratesAdditvely (2 : ZMod 48)) := by
  simp [GeneratesAdditvely]
  use 1
  intro x
  by_contra h;
  have h' : x * 2 ≡ 1 [ZMOD 48] := by
    erw [ ← ZMod.intCast_eq_intCast_iff ]
    norm_num
    exact h
  have := congr_arg ( · % 2 ) h'
  norm_num at this

example : ¬ GeneratesAdditvely (3 : ZMod 48) := by
  simp [GeneratesAdditvely]
  use 1;
  intro x
  by_contra h;
  have h' : x * 3 ≡ 1 [ZMOD 48] := by
    erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
  rw [ Int.ModEq ] at h'
  have := congr_arg ( · % 3 ) h'
  norm_num at this

example : GeneratesAdditvely (5 : ZMod 48) := by
  intro h
  use 29 * h.val
  simp [mul_assoc]
  grind


-- Exercise 3, p60
-- Find all generators for Z/48Z
example : Nat.card { g : ZMod 48 | GeneratesAdditvely g } = 16 := by
  unfold GeneratesAdditvely; norm_num [ Nat.card_eq_fintype_card ] ;
  have h_set : {g : ZMod 48 | ∀ h : ZMod 48, ∃ n : ℤ, (n : ZMod 48) * g = h} =
      {g : ZMod 48 | IsUnit g} := by
    ext g
    simp_all
    constructor
    · intro a
      obtain ⟨ n, hn ⟩ := a 1;
      grind [isUnit_of_dvd_one, dvd_of_mul_left_eq]
    · intro a h
      obtain ⟨ k, hk ⟩ := a.exists_left_inv
      use k.val * h.val
      simp
      grind

  convert Nat.card_eq_finsetCard _;
  any_goals exact Finset.filter ( fun x => IsUnit x ) ( Finset.univ : Finset ( ZMod 48 ) );
  · rw [ Set.ext_iff ] at h_set ; aesop;
  · decide +kernel
