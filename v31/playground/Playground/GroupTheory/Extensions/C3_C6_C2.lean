import Mathlib

abbrev C2 := Multiplicative (ZMod 2)
abbrev C3 := Multiplicative (ZMod 3)
abbrev C6 := Multiplicative (ZMod 6)

/-!
C6 is an extension of C2 by C3

Key definitions
- `C2_extension`: the extension of C2
-/
def f : C3 →* C6 := {
  toFun x := match (x.toAdd) with
  | 0 => (.ofAdd 0)
  | 1 => (.ofAdd 2)
  | 2 => (.ofAdd 4)
  map_one' := by decide
  map_mul' := by decide
}

lemma f_injective : Function.Injective f := by decide

def g : C6 →* C2 := {
  toFun x := match (x.toAdd) with
  | 0 => (.ofAdd 0)
  | 1 => (.ofAdd 1)
  | 2 => (.ofAdd 0)
  | 3 => (.ofAdd 1)
  | 4 => (.ofAdd 0)
  | 5 => (.ofAdd 1)
  map_one' := by decide
  map_mul' := by decide
}

lemma g_surjective : Function.Surjective g := by
  intro y
  fin_cases y <;> decide

def im_f : Subgroup C6 := {
  carrier := { .ofAdd 0, .ofAdd 2, .ofAdd 4 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide
}

lemma f_im_eq_im_f : f.range = im_f := by
  ext x
  simp [f, im_f]
  decide +revert

lemma ker_g_eq_im_f : g.ker = im_f := by
  ext x
  simp [g, im_f]
  decide +revert

def C3_C6_C2 : GroupExtension C3 C6 C2 := {
  inl := f
  rightHom := g
  inl_injective := f_injective
  range_inl_eq_ker_rightHom := by
    grind [f_im_eq_im_f, ker_g_eq_im_f]
  rightHom_surjective := g_surjective
}
