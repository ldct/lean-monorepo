import Mathlib


def MyCentralizer {G} [Group G] (A : Set G) : Subgroup G := {
  carrier := { g : G | ∀ a ∈ A, g * a * g⁻¹ = a }
  mul_mem' := by
    intro x y hx hy
    simp at *
    intro a ha
    nth_rw 2 [← hx a ha]
    nth_rw 2 [← hy a ha]
    group
  one_mem' := by
    intro a ha
    group
  inv_mem' := by
    intro x hx a ha
    simp at *
    nth_rw 1 [← hx a ha]
    group
}

def MyCenter (G) [Group G] : Subgroup G := {
  carrier := { g : G | ∀ a : G, g * a * g⁻¹ = a }
  mul_mem' := by
    intro x y hx hy
    simp at *
    intro a
    nth_rw 2 [← hx a, ← hy a]
    group
  one_mem' := by
    intro a
    group
  inv_mem' := by
    intro x hx a
    simp at *
    nth_rw 1 [← hx a]
    group
}

example {G} [Group G] : (MyCenter G) = (MyCentralizer ⊤) := by
  simp [MyCenter, MyCentralizer]

def MyMap {G} [Group G] (h : G) (A : Set G) (g : G) : Set G :=
  { h * a * g | a ∈ A }

def Normalizes {G} [Group G] (g : G) (A : Set G) : Prop := MyMap g A g⁻¹ = A

example {G} [Group G] (A : Set G) (g : G) (hg : Normalizes g A) : Normalizes g⁻¹ A := by
  sorry
