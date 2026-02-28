import Mathlib

set_option linter.style.longLine false


namespace GaussianIntegers_grind

/-
# Key definitions

- `GaussInt` is the type of Gaussian integers
- `instance CommRing GaussInt`

Every proof of the instance is done by `grind`; as of v24, this takes 20k heartbeats to verify, with `grind`.
-/

@[grind ext]
structure GaussInt where
  re : ℤ
  im : ℤ

instance : Zero GaussInt := ⟨⟨0, 0⟩⟩

instance : One GaussInt := ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

@[grind =]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[grind =]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[grind =]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[grind =]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[grind =]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[grind =]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[grind =]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[grind =]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[grind =]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[grind =]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_comm := by grind
  mul_assoc := by grind
  one_mul := by grind
  mul_one := by grind
  left_distrib := by grind
  right_distrib := by grind
  mul_comm := by grind
  zero_mul := by grind
  mul_zero := by grind


end GaussianIntegers_grind