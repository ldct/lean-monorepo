import Playground.Lagarias.LandauPoles
import Playground.Lagarias.LandauContinuation

/-!
# The differential pole obstruction

Blueprint: Proposition 10.4. A pole of `Q` becomes a pole of strictly higher
order in `Q - Q'`, so this expression cannot be the second derivative of a
holomorphic function. This handles all pole multiplicities using orders,
without postulating a nonzero residue or treating totalized values as limits.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open Filter Set
open scoped Topology

/-- Differentiation dominates the original function at any pole. -/
theorem order_sub_deriv_of_pole {Q : ℂ → ℂ} {z : ℂ} {m : ℤ}
    (hm : m < 0) (horder : meromorphicOrderAt Q z = (m : WithTop ℤ)) :
    meromorphicOrderAt (Q - deriv Q) z = ((m - 1 : ℤ) : WithTop ℤ) := by
  have hne : meromorphicOrderAt Q z ≠ 0 := by
    rw [horder]
    exact_mod_cast (ne_of_lt hm)
  have hQ : MeromorphicAt Q z := meromorphicAt_of_meromorphicOrderAt_ne_zero hne
  have hd := meromorphicOrderAt_deriv_eq_sub_one
    (Int.cast_ne_zero.mpr (ne_of_lt hm) : (m : ℂ) ≠ 0) horder
  have hnd : meromorphicOrderAt (-deriv Q) z = ((m - 1 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_neg (f := deriv Q)).symm.trans hd
  rw [sub_eq_add_neg]
  have hlt : meromorphicOrderAt (-deriv Q) z < meromorphicOrderAt Q z := by
    rw [hnd, horder]
    exact_mod_cast (show m - 1 < m by omega)
  exact (meromorphicOrderAt_add_eq_right_of_lt hQ hlt).trans hnd

/-- In particular, a simple pole of `Q` becomes a genuine double pole in `Q-Q'`. -/
lemma order_sub_deriv_of_simple_pole {Q : ℂ → ℂ} {z : ℂ}
    (horder : meromorphicOrderAt Q z = ((-1 : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt (Q - deriv Q) z = ((-2 : ℤ) : WithTop ℤ) := by
  simpa using order_sub_deriv_of_pole (by norm_num : (-1 : ℤ) < 0) horder

/-- A meromorphic differential identity initially known at one point propagates
through a connected domain. Its right side cannot have a pole if the left side
is the second derivative of a holomorphic function. -/
theorem no_second_primitive_of_pole {Q W : ℂ → ℂ} {U : Set ℂ} {x z : ℂ}
    (hQ : MeromorphicOn Q U) (hW : AnalyticOnNhd ℂ W U)
    (hU : IsPreconnected U) (hx : x ∈ U) (hz : z ∈ U)
    (heq : Q - deriv Q =ᶠ[𝓝[≠] x] deriv (deriv W))
    (hpole : meromorphicOrderAt Q z < 0) : False := by
  have hfinite : meromorphicOrderAt Q z ≠ ⊤ := ne_top_of_lt hpole
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hmneg : m < 0 := by
    rw [← hm] at hpole
    exact_mod_cast hpole
  have horder := order_sub_deriv_of_pole hmneg hm.symm
  have hR : MeromorphicOn (Q - deriv Q) U :=
    fun u hu => (hQ u hu).sub (hQ u hu).deriv
  have hD : MeromorphicOn (deriv (deriv W)) U :=
    fun u hu => (hW u hu).deriv.deriv.meromorphicAt
  have hgerm := meromorphic_germ_eq_of_preconnected hR hD hU hx hz heq
  have hnonneg := (hW z hz).deriv.deriv.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hgerm, horder] at hnonneg
  have : (0 : ℤ) ≤ m - 1 := by exact_mod_cast hnonneg
  omega

/-- The actual zeta expression from the convergent Chebyshev-error integral
has the double-pole obstruction at every zeta zero to the left of 1. -/
theorem psiErrorContinuation_sub_deriv_order_at_zero {z : ℂ}
    (hz : z.re < 1) (hζ : riemannZeta z = 0) :
    meromorphicOrderAt (psiErrorContinuation - deriv psiErrorContinuation) z =
      ((-2 : ℤ) : WithTop ℤ) :=
  order_sub_deriv_of_simple_pole (psiErrorContinuation_order_at_zeta_zero hz hζ)

end LeanEval.NumberTheory.Lagarias.Landau
