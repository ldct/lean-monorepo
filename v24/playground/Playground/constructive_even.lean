import Mathlib

set_option linter.style.longLine false

/-
This file is an exploration of effective algorithms for evenness, where we ban recursion and division and a proof for n(n+1) being even requires a proof for n being even or n+1 being even.
-/

structure EvenNumber where
  k : ℤ

structure OddNumber where
  k : ℤ

def evenNumber_off_even_add (a b : EvenNumber) : EvenNumber := {
  k := a.k + b.k
}

def evenNumber_off_odd_add (a b : OddNumber) : EvenNumber := {
  k := a.k + b.k + 1
}

def evenNumber_mul (a : EvenNumber) (b : ℤ) : EvenNumber := {
  k := a.k * b
}



def isEven_mul_self_succ (n : Int) : IsEven (n * (n + 1)) := {
  k := n * (n + 1) / 2
  ev := by
    have : Even (n * (n + 1)) := by
      by_cases h : Even n
      have : Even (n * (n + 1)) := by grind
      grind
      have : Even (n + 1) := by grind
      grind
    grind
}

theorem isEven_sqrt (n : Int) (h : IsEven (n * n)) : IsEven n := {
  k := (n + (n*n - n*n)) / 2
  ev := by
    obtain ⟨ k, hk ⟩ := h
    nth_rw 2 [hk]
    obtain ⟨ k, rfl ⟩ := h
    grind
}

def isEven_10 : IsEven 10 := isEven_add 4 6 isEven4 isEven6
#eval isEven_10.k








#eval 1 + 1
