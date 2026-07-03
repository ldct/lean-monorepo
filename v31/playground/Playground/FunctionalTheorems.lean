import Mathlib

example (A B : Type) [Nonempty A] (f : A → B) (h : Function.Bijective f) : Function.Surjective f.invFun := by
  grind [Function.invFun_surjective, Function.Bijective]

theorem invFun_surjective (T : Type) [Nonempty T] (f : T → T) (hf : Function.Injective f) : Function.Surjective (Function.invFun f) := by
  have h1 := Function.leftInverse_invFun hf
  grind [Function.leftInverse_invFun, Function.LeftInverse.surjective, Function.leftInverse_invFun]

theorem invFun_injective (T : Type) [Nonempty T] (f : T → T) (hf : Function.Surjective f) : Function.Injective (Function.invFun f) := by
  exact (Function.rightInverse_invFun hf).injective
