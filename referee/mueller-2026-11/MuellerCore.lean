import Mathlib

/-!
# Mueller, "The Lorentz Factor as the Slope of an Additional Spatial Coordinate" (Zenodo 10.5281/zenodo.24280888)
Machine-checked: the pure algebra / one-variable calculus behind eqs (14), (26), (21), (49), (89), (119)-(121),
(126), (137). It checks that the displayed identities follow from their stated premises.
DOES NOT CHECK: any physics (the Gauss equation of the embedding, the static vacuum Einstein equations, the
Painleve-Gullstrand form, Hypothesis M, Appendix A numerics, the claim of a derived lapse beyond the ODE step).
-/
namespace MuellerCore
open Real

/-- eq (13)/(14),(26): with `0 ≤ v < c`, `γ = 1/√(1 - v²/c²)` and `s = v/√(c²-v²)` (= ∂ₓy):
    `γ² = 1 + s²` and `s = γ v / c`. -/
theorem gamma_sq {v c : ℝ} (hc : 0 < c) (hv0 : 0 ≤ v) (hv : v < c) :
    (1 / Real.sqrt (1 - v^2/c^2))^2 = 1 + (v / Real.sqrt (c^2 - v^2))^2 := by
  have h1 : 0 < c^2 - v^2 := by nlinarith
  have h2 : 0 < 1 - v^2/c^2 := by
    have : v^2/c^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  rw [div_pow, div_pow, Real.sq_sqrt h2.le, Real.sq_sqrt h1.le]
  field_simp
  ring

theorem slope_eq {v c : ℝ} (hc : 0 < c) (hv0 : 0 ≤ v) (hv : v < c) :
    v / Real.sqrt (c^2 - v^2) = (1 / Real.sqrt (1 - v^2/c^2)) * v / c := by
  have h1 : 0 < c^2 - v^2 := by nlinarith
  have h2 : 0 < 1 - v^2/c^2 := by
    have : v^2/c^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have : Real.sqrt (c^2 - v^2) = c * Real.sqrt (1 - v^2/c^2) := by
    have e : c^2 - v^2 = c^2 * (1 - v^2/c^2) := by field_simp
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  rw [this]
  have hs : 0 < Real.sqrt (1 - v^2/c^2) := Real.sqrt_pos.mpr h2
  field_simp

/-- eq (18)-(21): for dt = 0 the transformed interval is -dx². -/
theorem interval_invariant {v c dx : ℝ} (hc : 0 < c) (hv0 : 0 ≤ v) (hv : v < c) :
    (-(1 / Real.sqrt (1 - v^2/c^2)) * (v/c) * dx)^2 - ((1 / Real.sqrt (1 - v^2/c^2)) * dx)^2 = -dx^2 := by
  have h2 : 0 < 1 - v^2/c^2 := by
    have : v^2/c^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hs : 0 < Real.sqrt (1 - v^2/c^2) := Real.sqrt_pos.mpr h2
  have hsq := Real.sq_sqrt h2.le
  generalize Real.sqrt (1 - v^2/c^2) = s at hs hsq
  have hg : (1/s)^2 * (1 - v^2/c^2) = 1 := by
    rw [div_pow, ← hsq]; field_simp
  generalize 1/s = g at hg
  linear_combination (-dx^2) * hg

/-- eq (49), (134): `1 + β²γ² = γ² = 1/(1-β²)` for `0 ≤ β² < 1`; with β² = rs/R this is the Schwarzschild g_RR. -/
theorem hRR {b2 : ℝ} (h : b2 < 1) : 1 + b2 * (1/(1-b2)) = 1/(1-b2) := by
  have : 1 - b2 ≠ 0 := by linarith
  field_simp; ring

/-- eq (144)-(146): the Flamm profile `y = 2√(rs(R-rs))` has slope `√(rs/(R-rs))`. -/
theorem flamm_deriv {rs R : ℝ} (hrs : 0 < rs) (hR : rs < R) :
    HasDerivAt (fun r => 2 * Real.sqrt (rs * (r - rs))) (Real.sqrt (rs / (R - rs))) R := by
  have hd : 0 < R - rs := by linarith
  have hpos : 0 < rs * (R - rs) := mul_pos hrs hd
  have h1 : HasDerivAt (fun r => rs * (r - rs)) rs R := by
    simpa using ((hasDerivAt_id R).sub_const rs).const_mul rs
  have h2 := (h1.sqrt hpos.ne').const_mul 2
  refine h2.congr_deriv ?_
  rw [Real.sqrt_div hrs.le, Real.sqrt_mul hrs.le]
  have a : 0 < Real.sqrt rs := Real.sqrt_pos.mpr hrs
  have b : 0 < Real.sqrt (R - rs) := Real.sqrt_pos.mpr hd
  have e : Real.sqrt rs * Real.sqrt rs = rs := Real.mul_self_sqrt hrs.le
  field_simp
  nlinarith [e]

/-- eq (88)-(89): `Φ = Phi0 + (Q/rs) ln(1 - rs/R)` satisfies `Φ' = Q/(R(R-rs))`. -/
theorem phi_deriv {rs Q Phi0 R : ℝ} (hrs : 0 < rs) (hR : rs < R) :
    HasDerivAt (fun r => Phi0 + Q / rs * Real.log (1 - rs / r)) (Q / (R * (R - rs))) R := by
  have hR0 : 0 < R := lt_trans hrs hR
  have hne : R ≠ 0 := hR0.ne'
  have h1 : HasDerivAt (fun r => 1 - rs / r) (rs / R^2) R := by
    have := (hasDerivAt_inv hne).const_mul rs
    have := this.const_sub 1
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using this
  have hpos : 1 - rs / R ≠ 0 := by
    have : rs / R < 1 := by rw [div_lt_one hR0]; exact hR
    linarith
  have h2 := (h1.log hpos).const_mul (Q / rs) |>.const_add Phi0
  refine h2.congr_deriv ?_
  have hd : R - rs ≠ 0 := by linarith
  have e : 1 - rs / R = (R - rs) / R := by field_simp
  rw [e]
  field_simp

/-- Prop. 1 (eq 121): for `N = √(1 - rs/R)`, `N'/N = rs / (2 R (R - rs))`. -/
theorem lapse_logderiv {rs R : ℝ} (hrs : 0 < rs) (hR : rs < R) :
    HasDerivAt (fun r => Real.sqrt (1 - rs / r)) (rs / (2 * R * (R - rs)) * Real.sqrt (1 - rs / R)) R := by
  have hR0 : 0 < R := lt_trans hrs hR
  have hne : R ≠ 0 := hR0.ne'
  have h1 : HasDerivAt (fun r => 1 - rs / r) (rs / R^2) R := by
    have := (hasDerivAt_inv hne).const_mul rs
    have := this.const_sub 1
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using this
  have hpos : 0 < 1 - rs / R := by
    have : rs / R < 1 := by rw [div_lt_one hR0]; exact hR
    linarith
  have h2 := h1.sqrt hpos.ne'
  refine h2.congr_deriv ?_
  have hd : R - rs ≠ 0 := by linarith
  have hs : 0 < Real.sqrt (1 - rs / R) := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  generalize Real.sqrt (1 - rs / R) = s at hs hsq ⊢
  have hsR : s^2 * R = R - rs := by rw [hsq]; field_simp
  field_simp
  nlinarith [hsR]

/-- eq (126): `3√(1 - rs/R) > 1  ↔  R > 9 rs / 8`. -/
theorem buchdahl_uniform {rs R : ℝ} (hrs : 0 < rs) (hR : rs < R) :
    1 < 3 * Real.sqrt (1 - rs / R) ↔ 9 * rs / 8 < R := by
  have hR0 : 0 < R := lt_trans hrs hR
  have hpos : 0 < 1 - rs / R := by
    have : rs / R < 1 := by rw [div_lt_one hR0]; exact hR
    linarith
  constructor
  · intro h
    have : (1:ℝ)/3 < Real.sqrt (1 - rs / R) := by linarith
    have h3 := (Real.lt_sqrt (by norm_num)).mp this
    have : 1/9 < 1 - rs/R := by nlinarith
    have : rs / R < 8/9 := by linarith
    rw [div_lt_iff₀ hR0] at this
    linarith
  · intro h
    have : rs / R < 8/9 := by rw [div_lt_iff₀ hR0]; linarith
    have : (1/3:ℝ)^2 < 1 - rs/R := by nlinarith
    have := (Real.lt_sqrt (by norm_num)).mpr this
    linarith

/-- Sciama identity (137): critical density `ρ = 3H²/(8πG)`, `m = (4π/3)ρ (c/H)³`: `G m /(c² (c/H)) = 1/2`
    and `r_s = c/H`. -/
theorem sciama {G c H : ℝ} (hG : 0 < G) (hc : 0 < c) (hH : 0 < H) :
    G * ((4 * Real.pi / 3) * (3 * H^2 / (8 * Real.pi * G)) * (c / H)^3) / (c^2 * (c / H)) = 1 / 2 := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  norm_num

/-- eq (68)->(72): solving (65),(66) for □Φ and inserting T = -ε+3p, T₄₄ = Φ² p_y. -/
theorem scalar_source {κ Φ ε p py boxΦ : ℝ} (hΦ : Φ ≠ 0)
    (h66 : -(-2 * κ * (Φ^2 * py) / Φ^2) + 3 / Φ * boxΦ = κ * (-ε + 3 * p)) :
    boxΦ = -(κ * Φ / 3) * (ε - 3 * p + 2 * py) := by
  field_simp at h66 ⊢
  nlinarith [h66]

/-- eq (140): `(v/c)⁴ = G M g₀ / c⁴` with `g₀ = κ' c H` equals `(κ'/2)·β_N²·β_H` with `β_N² = 2GM/(c²R)`, `β_H = HR/c`. -/
theorem deepMOND {G M c H κ R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    G * M * (κ * c * H) / c^4 = κ / 2 * ((2 * G * M / (c^2 * R)) * (H * R / c)) := by
  field_simp

end MuellerCore

#print axioms MuellerCore.gamma_sq
#print axioms MuellerCore.slope_eq
#print axioms MuellerCore.interval_invariant
#print axioms MuellerCore.hRR
#print axioms MuellerCore.flamm_deriv
#print axioms MuellerCore.phi_deriv
#print axioms MuellerCore.lapse_logderiv
#print axioms MuellerCore.buchdahl_uniform
#print axioms MuellerCore.sciama
#print axioms MuellerCore.scalar_source
#print axioms MuellerCore.deepMOND
