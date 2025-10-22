import Mathlib

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
  add_assoc := by #count_heartbeats! in grind
  zero_add := by #count_heartbeats! in grind
  add_zero := by #count_heartbeats! in grind
  neg_add_cancel := by #count_heartbeats! in grind
  add_comm := by #count_heartbeats! in grind
  mul_assoc := by #count_heartbeats! in grind
  one_mul := by #count_heartbeats! in grind
  mul_one := by #count_heartbeats! in grind
  left_distrib := by #count_heartbeats! in grind
  right_distrib := by #count_heartbeats! in grind
  mul_comm := by #count_heartbeats! in grind
  zero_mul := by #count_heartbeats! in grind
  mul_zero := by #count_heartbeats! in grind
