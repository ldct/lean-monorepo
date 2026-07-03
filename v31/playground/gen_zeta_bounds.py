#!/usr/bin/env python3
"""Generate Lean files for zeta(s) bounds for odd s >= 9.

Reads Zeta5Bounds.lean as a template and performs structured substitutions.
"""

from sympy import symbols, simplify, factor, Poly, expand, Rational, quo
from fractions import Fraction
import re

x = symbols('x')

def get_poly_coeffs_lo_to_hi(poly):
    """Get polynomial coefficients [a0, a1, ..., an] from lowest to highest degree."""
    d = poly.degree()
    return [int(poly.nth(i)) for i in range(d + 1)]

def format_lean_poly(coeffs, var="(N : \u211d)"):
    """Format polynomial as Lean expression."""
    terms = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        if i == 0:
            terms.append(str(c))
        elif i == 1:
            terms.append(f"{c} * {var}" if c != 1 else var)
        else:
            terms.append(f"{c} * {var} ^ {i}" if c != 1 else f"{var} ^ {i}")
    return " + ".join(terms)

def compute_data(s):
    """Compute all data needed for zeta(s) bounds."""
    sm1 = s - 1
    N = 23
    
    # Symbolic fraction identities
    lo_expr = (1/x**s + Rational(1,sm1)/(x+1)**sm1 + Rational(1,2)/(x+1)**s 
               - Rational(1,sm1)/x**sm1 - Rational(1,2)/x**s)
    hi_expr = (1/(x+1)**s + Rational(1,sm1)/(x+1)**sm1 - Rational(1,sm1)/x**sm1)
    
    lo_num_full = simplify(lo_expr * sm1 * x**s * (x+1)**s)
    hi_num_full = simplify(hi_expr * sm1 * x**sm1 * (x+1)**s)
    
    lo_P_poly = quo(Poly(expand(lo_num_full), x), Poly(2*x+1, x), x)
    lo_P_coeffs = get_poly_coeffs_lo_to_hi(lo_P_poly)
    
    hi_Q_poly = Poly(expand(-hi_num_full), x)
    hi_Q_coeffs = get_poly_coeffs_lo_to_hi(hi_Q_poly)
    
    # Numerical bounds
    lo_val = (sum(Fraction(1, k**s) for k in range(1, N)) + 
              Fraction(1, sm1 * N**sm1) + Fraction(1, 2 * N**s))
    hi_val = (sum(Fraction(1, k**s) for k in range(1, N+1)) + 
              Fraction(1, sm1 * N**sm1))
    
    best_d = 4
    best_lo_int = best_hi_int = 0
    for d in range(4, 12):
        denom = 10**d
        lo_int = int(float(lo_val) * denom)
        hi_int = lo_int + 1
        if lo_val >= Fraction(lo_int, denom) and hi_val <= Fraction(hi_int, denom) and denom <= 10**10:
            best_d, best_lo_int, best_hi_int = d, lo_int, hi_int
    
    return {
        's': s, 'sm1': sm1, 'N': N,
        'lo_poly': format_lean_poly(lo_P_coeffs, "x"),
        'hi_poly': format_lean_poly(hi_Q_coeffs, "x"),
        'lo_poly_N': format_lean_poly(lo_P_coeffs, "(N : \u211d)"),
        'hi_poly_N': format_lean_poly(hi_Q_coeffs, "(N : \u211d)"),
        'lo_int': best_lo_int, 'hi_int': best_hi_int, 'denom': 10**best_d,
        'dp': best_d,
    }

def generate_file(s):
    """Generate Lean file content for zeta(s)."""
    # Read Zeta5Bounds as template
    with open('Playground/Zeta5Bounds.lean', 'r') as f:
        template = f.read()
    
    d = compute_data(s)
    d5 = compute_data(5)  # reference data for s=5
    
    out = template
    
    # Replace docstring
    out = out.replace('\u03b6(5)', f'\u03b6({s})')
    out = out.replace('Zeta5Bounds', f'Zeta{s}Bounds')
    out = out.replace('zeta5', f'zeta{s}')
    out = out.replace('\u03b65', f'\u03b6{s}')
    out = out.replace('fifth', f'pow{s}')
    out = out.replace('inv_fifth', f'inv_pow{s}')
    
    # Replace exponents: ^ 5 -> ^ s, ^ 4 -> ^ sm1 in key places
    # This is tricky - need to be careful about context
    # Instead, let's just generate from scratch using the working pattern
    
    return None  # Fall back to direct generation


def generate_file_direct(s):
    """Generate Lean file directly."""
    d = compute_data(s)
    sm1 = d['sm1']
    
    # The e3 clearing step for lo: 1/(2*(x+1)^s) * (sm1 * x^s * (x+1)^s) = sm1*x^s/2
    # Need sm1/2 as integer if sm1 is even, else as fraction
    sm1_half = f"{sm1} * x ^ {s} / 2" if sm1 % 2 == 0 else f"{sm1} * x ^ {s} / 2"
    sm1_half_hi = f"{sm1} * (x + 1) ^ {s} / 2"
    
    return f"""import Mathlib


open Real Finset Filter Topology

/-!
# Upper and Lower bounds for \u03b6({s})

## Key theorems

- `zeta{s}_lo` : `({d['lo_int']} : \u211d) / {d['denom']} \u2264 (riemannZeta {s}).re`
- `zeta{s}_hi` : `(riemannZeta {s}).re \u2264 ({d['hi_int']} : \u211d) / {d['denom']}`

Same Euler-Maclaurin approach as Zeta3Bounds. N = {d['N']} gives {d['dp']} decimal places.
-/

namespace Zeta{s}Bounds

lemma summable_real :
    Summable (fun n : \u2115 => 1 / ((n : \u211d) + 1) ^ {s}) := by
  have h : Summable (fun n : \u2115 => 1 / (n : \u211d) ^ {s}) :=
    (Real.summable_one_div_nat_pow (p := {s})).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : \u211d) ^ {s}) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_cpow :
    Summable (fun n : \u2115 => 1 / ((n : \u2102) + 1) ^ ({s} : \u2102)) := by
  have hrec : 1 < ({s} : \u2102).re := by simp
  rw [show (fun n : \u2115 => 1 / ((n : \u2102) + 1) ^ ({s} : \u2102)) =
    (fun n : \u2115 => 1 / (n : \u2102) ^ ({s} : \u2102)) \u2218 (\u00b7 + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma re_eq_tsum :
    (riemannZeta {s}).re = \u2211' n : \u2115, 1 / ((n : \u211d) + 1) ^ {s} := by
  have hrec : 1 < ({s} : \u2102).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : \u2200 n : \u2115, (1 / ((n : \u2102) + 1) ^ ({s} : \u2102)).re = 1 / ((n : \u211d) + 1) ^ {s} := by
    intro n
    rw [show ((n : \u2102) + 1) ^ ({s} : \u2102) = ((((n : \u211d) + 1) ^ {s} : \u211d) : \u2102) from by
      rw [show ({s} : \u2102) = (({s} : \u2115) : \u2102) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : \u2102) / ((((n : \u211d) + 1) ^ {s} : \u211d) : \u2102) = ((1 / ((n : \u211d) + 1) ^ {s} : \u211d) : \u2102) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum :
    Tendsto (fun N : \u2115 => \u2211 k \u2208 range N, 1 / ((k : \u211d) + 1) ^ {s})
      atTop (𝓝 (riemannZeta {s}).re) := by
  rw [\u2190 hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [re_eq_tsum]; exact summable_real.hasSum

noncomputable def S_lo (N : \u2115) : \u211d :=
  (range (N - 1)).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) +
    1 / ({sm1} * (N : \u211d) ^ {sm1}) + 1 / (2 * (N : \u211d) ^ {s})

noncomputable def S_hi (N : \u2115) : \u211d :=
  (range N).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) +
    1 / ({sm1} * (N : \u211d) ^ {sm1})

private lemma lo_frac_identity (x : \u211d) (hx : x \u2260 0) (hx1 : x + 1 \u2260 0) :
    1 / x ^ {s} + 1 / ({sm1} * (x + 1) ^ {sm1}) + 1 / (2 * (x + 1) ^ {s}) -
    1 / ({sm1} * x ^ {sm1}) - 1 / (2 * x ^ {s}) =
    (2 * x + 1) * ({d['lo_poly']}) /
      ({sm1} * x ^ {s} * (x + 1) ^ {s}) := by
  rw [eq_div_iff (by positivity : ({sm1} : \u211d) * x ^ {s} * (x + 1) ^ {s} \u2260 0)]
  have e1 : 1 / x ^ {s} * ({sm1} * x ^ {s} * (x + 1) ^ {s}) = {sm1} * (x + 1) ^ {s} := by
    rw [one_div, show {sm1} * x ^ {s} * (x + 1) ^ {s} = x ^ {s} * ({sm1} * (x + 1) ^ {s}) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  have e2 : 1 / ({sm1} * (x + 1) ^ {sm1}) * ({sm1} * x ^ {s} * (x + 1) ^ {s}) = x ^ {s} * (x + 1) := by
    rw [one_div, show {sm1} * x ^ {s} * (x + 1) ^ {s} = ({sm1} * (x + 1) ^ {sm1}) * (x ^ {s} * (x + 1)) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ {s}) * ({sm1} * x ^ {s} * (x + 1) ^ {s}) = {sm1} * x ^ {s} / 2 := by
    rw [one_div, show {sm1} * x ^ {s} * (x + 1) ^ {s} = (2 * (x + 1) ^ {s}) * ({sm1} * x ^ {s} / 2) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  have e4 : 1 / ({sm1} * x ^ {sm1}) * ({sm1} * x ^ {s} * (x + 1) ^ {s}) = x * (x + 1) ^ {s} := by
    rw [one_div, show {sm1} * x ^ {s} * (x + 1) ^ {s} = ({sm1} * x ^ {sm1}) * (x * (x + 1) ^ {s}) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  have e5 : 1 / (2 * x ^ {s}) * ({sm1} * x ^ {s} * (x + 1) ^ {s}) = {sm1} * (x + 1) ^ {s} / 2 := by
    rw [one_div, show {sm1} * x ^ {s} * (x + 1) ^ {s} = (2 * x ^ {s}) * ({sm1} * (x + 1) ^ {s} / 2) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : \u211d) (hx : x \u2260 0) (hx1 : x + 1 \u2260 0) :
    1 / (x + 1) ^ {s} + 1 / ({sm1} * (x + 1) ^ {sm1}) - 1 / ({sm1} * x ^ {sm1}) =
    -({d['hi_poly']}) /
      ({sm1} * x ^ {sm1} * (x + 1) ^ {s}) := by
  rw [eq_div_iff (by positivity : ({sm1} : \u211d) * x ^ {sm1} * (x + 1) ^ {s} \u2260 0)]
  have e1 : 1 / (x + 1) ^ {s} * ({sm1} * x ^ {sm1} * (x + 1) ^ {s}) = {sm1} * x ^ {sm1} := by
    rw [one_div, show {sm1} * x ^ {sm1} * (x + 1) ^ {s} = (x + 1) ^ {s} * ({sm1} * x ^ {sm1}) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  have e2 : 1 / ({sm1} * (x + 1) ^ {sm1}) * ({sm1} * x ^ {sm1} * (x + 1) ^ {s}) = x ^ {sm1} * (x + 1) := by
    rw [one_div, show {sm1} * x ^ {sm1} * (x + 1) ^ {s} = ({sm1} * (x + 1) ^ {sm1}) * (x ^ {sm1} * (x + 1)) from by ring,
      inv_mul_cancel_left\u2080 (by positivity)]
  have e3 : 1 / ({sm1} * x ^ {sm1}) * ({sm1} * x ^ {sm1} * (x + 1) ^ {s}) = (x + 1) ^ {s} := by
    rw [one_div, inv_mul_cancel_left\u2080 (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

lemma S_lo_step (N : \u2115) (hN : 1 \u2264 N) :
    S_lo (N + 1) - S_lo N =
      (2 * (N : \u211d) + 1) * ({d['lo_poly_N']}) /
        ({sm1} * (N : \u211d) ^ {s} * ((N : \u211d) + 1) ^ {s}) := by
  have hN' : (N : \u211d) \u2260 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : \u211d) + 1 \u2260 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) +
      1 / ({sm1} * ((N + 1 : \u2115) : \u211d) ^ {sm1}) + 1 / (2 * ((N + 1 : \u2115) : \u211d) ^ {s}) -
    ((range (N - 1)).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) +
      1 / ({sm1} * (N : \u211d) ^ {sm1}) + 1 / (2 * (N : \u211d) ^ {s})) =
    (2 * (N : \u211d) + 1) * ({d['lo_poly_N']}) /
      ({sm1} * (N : \u211d) ^ {s} * ((N : \u211d) + 1) ^ {s})
  simp only [show (N + 1 : \u2115) - 1 = N from by omega,
    show ((N + 1 : \u2115) : \u211d) = (N : \u211d) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) =
      (range (N - 1)).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) + 1 / (N : \u211d) ^ {s} := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (\u2191(N - 1) + 1 : \u211d) = (\u2191N : \u211d) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : \u211d) hN' hN1]

lemma S_hi_step (N : \u2115) (hN : 1 \u2264 N) :
    S_hi (N + 1) - S_hi N =
      -({d['hi_poly_N']}) /
        ({sm1} * (N : \u211d) ^ {sm1} * ((N : \u211d) + 1) ^ {s}) := by
  have hN' : (N : \u211d) \u2260 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : \u211d) + 1 \u2260 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) +
      1 / ({sm1} * ((N + 1 : \u2115) : \u211d) ^ {sm1}) -
    ((range N).sum (fun k => 1 / ((k : \u211d) + 1) ^ {s}) +
      1 / ({sm1} * (N : \u211d) ^ {sm1})) =
    -({d['hi_poly_N']}) /
      ({sm1} * (N : \u211d) ^ {sm1} * ((N : \u211d) + 1) ^ {s})
  rw [show ((N + 1 : \u2115) : \u211d) = (N : \u211d) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : \u211d) hN' hN1]

lemma S_lo_step_pos (N : \u2115) (hN : 1 \u2264 N) : S_lo N < S_lo (N + 1) := by
  have h := S_lo_step N hN
  have hNpos : (0 : \u211d) < N := Nat.cast_pos.mpr (by omega)
  have : (0 : \u211d) < (2 * N + 1) * ({d['lo_poly_N']}) /
      ({sm1} * N ^ {s} * (N + 1) ^ {s}) := by positivity
  linarith

lemma S_hi_step_neg (N : \u2115) (hN : 1 \u2264 N) : S_hi (N + 1) < S_hi N := by
  have h := S_hi_step N hN
  have hNpos : (0 : \u211d) < N := Nat.cast_pos.mpr (by omega)
  have hnum : ({d['hi_poly_N']}) > 0 := by positivity
  have : -({d['hi_poly_N']}) /
      ({sm1} * (N : \u211d) ^ {sm1} * ((N : \u211d) + 1) ^ {s}) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

lemma S_lo_strictMono : StrictMono (fun N => S_lo (N + 1)) :=
  strictMono_nat_of_lt_succ (fun n => S_lo_step_pos (n + 1) (by omega))

lemma S_hi_strictAnti : StrictAnti (fun N => S_hi (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => S_hi_step_neg (n + 1) (by omega))

private lemma tendsto_correction (c : \u211d) (hc : 0 < c) (p : \u2115) (hp : 0 < p) :
    Tendsto (fun N : \u2115 => 1 / (c * ((N : \u211d) + 1) ^ p)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop hc
      ((tendsto_pow_atTop (by omega : p \u2260 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

lemma S_lo_tendsto :
    Tendsto (fun N => S_lo (N + 1)) atTop (𝓝 (riemannZeta {s}).re) := by
  unfold S_lo
  simp_rw [show \u2200 N : \u2115, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : \u2115 =>
      (\u2211 k \u2208 range N, 1 / ((k : \u211d) + 1) ^ {s}) +
      (1 / ({sm1} * ((N : \u211d) + 1) ^ {sm1}) + 1 / (2 * ((N : \u211d) + 1) ^ {s})))
      atTop (𝓝 (riemannZeta {s}).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta {s}).re = (riemannZeta {s}).re + (0 + 0) from by ring]
  exact tendsto_partial_sum.add
    ((tendsto_correction {sm1} (by norm_num) {sm1} (by norm_num)).add
      (tendsto_correction 2 (by norm_num) {s} (by norm_num)))

lemma S_hi_tendsto :
    Tendsto (fun N => S_hi (N + 1)) atTop (𝓝 (riemannZeta {s}).re) := by
  unfold S_hi
  suffices h : Tendsto (fun N : \u2115 =>
      (\u2211 k \u2208 range (N + 1), 1 / ((k : \u211d) + 1) ^ {s}) +
      1 / ({sm1} * ((N : \u211d) + 1) ^ {sm1}))
      atTop (𝓝 (riemannZeta {s}).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta {s}).re = (riemannZeta {s}).re + 0 from by ring]
  exact (tendsto_partial_sum.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction {sm1} (by norm_num) {sm1} (by norm_num))

lemma S_lo_le (N : \u2115) (hN : 1 \u2264 N) :
    S_lo N \u2264 (riemannZeta {s}).re := by
  obtain \u27e8m, rfl\u27e9 : \u2203 m, N = m + 1 := \u27e8N - 1, by omega\u27e9
  exact ge_of_tendsto S_lo_tendsto
    (eventually_atTop.mpr \u27e8m, fun k hk => S_lo_strictMono.monotone hk\u27e9)

lemma S_hi_ge (N : \u2115) (hN : 1 \u2264 N) :
    (riemannZeta {s}).re \u2264 S_hi N := by
  obtain \u27e8m, rfl\u27e9 : \u2203 m, N = m + 1 := \u27e8N - 1, by omega\u27e9
  exact le_of_tendsto S_hi_tendsto
    (eventually_atTop.mpr \u27e8m, fun k hk => S_hi_strictAnti.antitone hk\u27e9)

def S_lo_q : \u211a :=
  (range 22).sum (fun k => 1 / ((k + 1 : \u211a)) ^ {s}) +
    1 / ({sm1} * 23 ^ {sm1}) + 1 / (2 * 23 ^ {s})

def S_hi_q : \u211a :=
  (range 23).sum (fun k => 1 / ((k + 1 : \u211a)) ^ {s}) +
    1 / ({sm1} * 23 ^ {sm1})

set_option maxHeartbeats 4000000 in
lemma S_lo_q_ge : {d['lo_int']} / {d['denom']} \u2264 S_lo_q := by norm_num [S_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma S_hi_q_le : S_hi_q \u2264 {d['hi_int']} / {d['denom']} := by norm_num [S_hi_q, Finset.sum_range_succ]

lemma S_lo_q_cast : (S_lo_q : \u211d) = S_lo 23 := by
  simp only [S_lo_q, S_lo]; push_cast; norm_num

lemma S_hi_q_cast : (S_hi_q : \u211d) = S_hi 23 := by
  simp only [S_hi_q, S_hi]; push_cast; norm_num

lemma S_lo_23_ge : ({d['lo_int']} : \u211d) / {d['denom']} \u2264 S_lo 23 := by
  rw [\u2190 S_lo_q_cast,
    show ({d['lo_int']} : \u211d) / {d['denom']} = (({d['lo_int']} / {d['denom']} : \u211a) : \u211d) from by push_cast; ring]
  exact_mod_cast S_lo_q_ge

lemma S_hi_23_le : S_hi 23 \u2264 ({d['hi_int']} : \u211d) / {d['denom']} := by
  rw [\u2190 S_hi_q_cast,
    show ({d['hi_int']} : \u211d) / {d['denom']} = (({d['hi_int']} / {d['denom']} : \u211a) : \u211d) from by push_cast; ring]
  exact_mod_cast S_hi_q_le

end Zeta{s}Bounds

open Zeta{s}Bounds in
theorem zeta{s}_lo : ({d['lo_int']} : \u211d) / {d['denom']} \u2264 (riemannZeta {s}).re :=
  calc ({d['lo_int']} : \u211d) / {d['denom']}
      _ \u2264 S_lo 23 := S_lo_23_ge
      _ \u2264 (riemannZeta {s}).re := S_lo_le 23 (by norm_num)

open Zeta{s}Bounds in
theorem zeta{s}_hi : (riemannZeta {s}).re \u2264 ({d['hi_int']} : \u211d) / {d['denom']} :=
  calc (riemannZeta {s}).re \u2264 S_hi 23 := S_hi_ge 23 (by norm_num)
    _ \u2264 {d['hi_int']} / {d['denom']} := S_hi_23_le
"""

if __name__ == "__main__":
    for s in [9, 11, 13, 15, 17, 19, 21]:
        filename = f"Playground/Zeta{s}Bounds.lean"
        content = generate_file_direct(s)
        with open(filename, 'w') as f:
            f.write(content)
        print(f"Generated {filename} ({len(content)} bytes)")
