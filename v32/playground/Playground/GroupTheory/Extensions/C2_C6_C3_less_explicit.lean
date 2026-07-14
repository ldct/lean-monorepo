import Mathlib

abbrev C2 := Multiplicative (ZMod 2)
abbrev C3 := Multiplicative (ZMod 3)
abbrev C6 := Multiplicative (ZMod 6)

/-!
C6 is an extension of C3 by C2

Uses less explicit definitions

Key definitions
- `C3_extension`: the extension of C3
-/

def f : C2 →* C6 where
  toFun x := Multiplicative.ofAdd (3 * (x.toAdd.val : ZMod 6))
  map_one' := by decide
  map_mul' := by decide

lemma f_injective : Function.Injective f := by
  intro a b h
  decide +revert

def g : C6 →* C3 := {
  toFun x := .ofAdd (x.toAdd).val
  map_one' := by decide
  map_mul' := by decide
}

lemma g_surjective : Function.Surjective g := by
  intro y
  fin_cases y <;> decide

def im_f : Subgroup C6 := {
  carrier := { .ofAdd 0, .ofAdd 3 }
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

def C2_C6_C3 : GroupExtension C2 C6 C3 := {
  inl := f
  rightHom := g
  inl_injective := f_injective
  range_inl_eq_ker_rightHom := by
    grind [f_im_eq_im_f, ker_g_eq_im_f]
  rightHom_surjective := g_surjective
}
