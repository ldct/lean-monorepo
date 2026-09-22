# Pinned Hadamard compatibility probe

Upstream `a5154676af9aa3095150ee410cdda80555aa0642`.
The project toolchain and Mathlib pin are not changed.

Minimal source closure: 61 modules.
Additional import roots: []
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CanonicalProduct`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorSupport`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.LocallyUniformLimit`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorUnits`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorComplement`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorPartialProductFactor`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientConvergence`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientRemovable`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Topology.MetricSpace.Annulus`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.PosLog`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Growth`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorHolomorphic`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Dyadic`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Summability`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.AbsMax`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanBound`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanInverseFactorBound`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanMajorantBound`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanProductBound`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.BorelCaratheodory`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ExpPoly`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ExpPoly.Growth`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Growth`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFunctionalEquation`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Trigonometric`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GammaBounds`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.GammaStirlingAux`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Real`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Convex`.
Compiled `PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegrableOn`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Algebra.Order.Floor.Ring`.
Compiled `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Deriv`.
Compiled `PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelKernel`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.AbelSummation`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaPartialSum`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaStripBound`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaValues`.
Compiled `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`.
## Capstone audit
```text
AUDITED riemannXi_entireOfOrderAtMost_one: [propext, Classical.choice, Quot.sound]
AUDITED summable_riemannXi_divisorZeroIndex₀_norm_inv_sq: [propext, Classical.choice, Quot.sound]
AUDITED riemannXi_hadamard_factorization_no_monomial: [propext, Classical.choice, Quot.sound]
AUDITED exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum: [propext, Classical.choice, Quot.sound]

```
