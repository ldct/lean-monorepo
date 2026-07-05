import Playground.Pi.Clausen

/-!
# The Picard–Fuchs differential equation

This file covers chapter 7 of Milla's proof of the Chudnovsky formula (arXiv:1809.00533v6,
`120_PicardFuchs.tex`).

## Main definitions

* `Chudnovsky.SatisfiesPicardFuchs` : the predicate that a function `Ω : ℂ → ℂ` satisfies the
  Picard–Fuchs differential equation
  `d²Ω/dJ² + (1/J)·dΩ/dJ + (31J - 4)/(144·J²·(J-1)²)·Ω = 0`
  on a set `S ⊆ ℂ` (paper Thm. `picardfuchs`).

## Main statements (`sorry`-stubbed)

* `Chudnovsky.exists_periods_satisfyPicardFuchs` : the paper's Thm. `picardfuchs` — the two
  basic periods `Ω₁, Ω₂` of the lattice `L_J` satisfy the Picard–Fuchs equation.

  The paper treats `Ω₁, Ω₂` as (multivalued) functions of `J`; globally `J ↦ (Ω₁, Ω₂)` is only
  well defined up to `SL₂(ℤ)` (e.g. `J(τ+1) = J(τ)` but `Ω₂ = √(g₃/g₂)·τ` changes), so we state
  the theorem *locally*: near every value `J(τ₀)`, `τ₀ ∈ Region`, there are holomorphic local
  branches of the periods, normalized as in the paper's table of lattices (ch. 9,
  `140_MainTheorem.tex`) by `(Ω₁, Ω₂) = √(g₃(τ)/g₂(τ)) · (1, τ)`; the normalization is recorded
  in the branch-free forms `Ω₁² = g₃/g₂` and `Ω₂ = τ·Ω₁`.

## Design notes (PLAN A7)

Two routes to prove this (and its consumer, `Kummer.lean`) are under consideration:

1. **Paper route (ch. 7)**: represent the periods as contour integrals `Ω_k = ∮ dx/y`
   (paper `satzint`), differentiate under the integral sign in the parameter
   `g = 27J/(J-1)`, use the exactness relations `∮ (xⁿ/y)' dx = 0` to solve a 3×3 linear
   system, and change variables `g ↔ J`. Requires period-integral machinery from
   `Quasiperiods.lean` (A2) that is not yet formalized.
2. **Recommended alternative (PLAN A7)**: bypass the Picard–Fuchs equation entirely and prove
   the chapter-8 output `E₄ = (₂F₁(1/12, 5/12; 1; 1/J))⁴` directly in `q`-space via Ramanujan's
   derivative identities (`D E₂ = (E₂² - E₄)/12`, etc.), turning everything into a
   formal-power-series uniqueness argument. In that case this file's theorem becomes a
   by-product / can be dropped from the main chain.

This file is deliberately minimal until that decision is made.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex

/-- The **Picard–Fuchs differential equation** (paper Thm. `picardfuchs`):
`Ω` satisfies `d²Ω/dJ² + (1/J)·dΩ/dJ + (31J - 4)/(144·J²·(J-1)²)·Ω = 0` at every point of `S`. -/
def SatisfiesPicardFuchs (Ω : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    deriv (deriv Ω) z + 1 / z * deriv Ω z
      + (31 * z - 4) / (144 * z ^ 2 * (z - 1) ^ 2) * Ω z = 0

/-- **Picard–Fuchs** (paper Thm. `picardfuchs`, ch. 7): the basic periods `Ω₁, Ω₂` of the
lattice `L_J` are solutions of the Picard–Fuchs differential equation.

Stated locally around `J(τ₀)` for `τ₀ ∈ Region` (where `J` is locally biholomorphic, since
`Region` contains no elliptic points): there exist holomorphic local branches `Ω₁, Ω₂` of the
periods of `L_J`, both solving the Picard–Fuchs equation, normalized at `τ₀` by the paper's
`(Ω₁, Ω₂) = √(g₃/g₂)·(1, τ)` — recorded branch-free as `Ω₁² = g₃/g₂` and `Ω₂ = τ₀·Ω₁`.

TODO: the global multivalued statement of the paper cannot be stated for single-valued
functions of `J`; this local form is what the Kummer chapter's ODE-uniqueness argument
consumes. Revisit once the route (contour integrals vs. Ramanujan identities, see module
docstring) is decided. -/
theorem exists_periods_satisfyPicardFuchs (τ₀ : ℍ) (hτ₀ : τ₀ ∈ Region) :
    ∃ (U : Set ℂ) (Ω₁ Ω₂ : ℂ → ℂ), IsOpen U ∧ J τ₀ ∈ U ∧
      DifferentiableOn ℂ Ω₁ U ∧ DifferentiableOn ℂ Ω₂ U ∧
      SatisfiesPicardFuchs Ω₁ U ∧ SatisfiesPicardFuchs Ω₂ U ∧
      Ω₁ (J τ₀) ^ 2 = (Lτ τ₀).g₃ / (Lτ τ₀).g₂ ∧
      Ω₂ (J τ₀) = (τ₀ : ℂ) * Ω₁ (J τ₀) := by
  sorry

end Chudnovsky
