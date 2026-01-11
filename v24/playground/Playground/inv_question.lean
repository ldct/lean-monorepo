
import Mathlib

example (A B : Type) [Nonempty A] (f : A → B) (h : f.Bijective)
:  (fun x ↦ Function.invFun f (f x)) = fun x ↦ x := by
  funext x; exact Function.leftInverse_invFun h.injective x

open Function

example (A B : Type) [Nonempty A] (f : A → B) (h : f.Injective)
: invFun f ∘ f = id := by
  exact funext <| leftInverse_invFun h

example (A B : Type) [Nonempty A] (f : A → B) (h : f.Surjective)
: f ∘ invFun f = id := by
  ext y
  exact Function.invFun_eq (h y)

example (A B : Type) [Nonempty A] (f : A → B)
: (f.Injective) ↔ (invFun f ∘ f = id) := by
  apply Iff.intro;
  · intro h_inj
    funext x
    apply leftInverse_invFun h_inj
  · intro h x y hxy;
    have := congr_fun h x
    have := congr_fun h y
    grind

example (A B : Type) [Nonempty A] (f : A → B)
: (f.Surjective) ↔ (f ∘ invFun f = id) := by
  apply Iff.intro;
  · intro h_surjective
    funext b
    apply Function.invFun_eq (h_surjective b);
  · intro h y
    use Function.invFun f y
    apply congr_fun h y
