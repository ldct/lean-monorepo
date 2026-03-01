import Playground.RealIsometry.Basic

#check RealIsometry

#check R3

instance : SMul RealIsometry R3 where
  smul f x := f.toFun x

lemma smul_eq (f : RealIsometry) (x : R3) : f • x = f.toFun x := rfl

instance : MulAction RealIsometry R3 where
  one_smul := by
    simp [one_eq, RealIsometry.identity, smul_eq]
  mul_smul := by
    simp [mul_eq, RealIsometry.comp, smul_eq]

#check MulAction.stabilizerEquivStabilizer.congr_simp
