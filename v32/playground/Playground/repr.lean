import Mathlib

structure Wrap where
  val : Equiv.Perm (Fin 3)

-- ok
#eval (c[0, 1, 2] : Equiv.Perm (Fin 3))

-- ok
#eval (⟨c[0, 1, 2]⟩ : Wrap).val

-- comment this out
unsafe instance : Repr Wrap := ⟨fun w p => reprPrec w.val p⟩

-- ok... for now
#eval (⟨c[0, 1, 2]⟩ : Wrap)
