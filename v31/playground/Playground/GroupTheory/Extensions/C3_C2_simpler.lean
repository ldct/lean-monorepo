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
  fin_cases a <;> fin_cases b
  <;> simp +decide at *

def g : C6 →* C3 := {
  toFun x := .ofAdd (x.toAdd).val
  map_one' := by decide
  map_mul' x y := by
    simp only [toAdd_mul]
    fin_cases x
    <;> fin_cases y
    <;> simp +decide
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
  constructor
  · rintro ⟨ a, ha ⟩
    fin_cases a <;> simp_all <;> rw [← ha] <;> decide
  · rintro h
    obtain rfl | rfl := h <;> decide

lemma ker_g_eq_im_f : g.ker = im_f := by
  ext x
  simp [g, im_f]
  constructor
  · intro h
    fin_cases x <;> simp_all +decide
  · rintro h
    obtain rfl | rfl := h <;> decide

def C3_extension : GroupExtension C2 C6 C3 := {
  inl := f
  rightHom := g
  inl_injective := f_injective
  range_inl_eq_ker_rightHom := by
    grind [f_im_eq_im_f, ker_g_eq_im_f]
  rightHom_surjective := g_surjective
}
