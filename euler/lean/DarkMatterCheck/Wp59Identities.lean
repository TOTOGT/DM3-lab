import Mathlib

/-
  Wp59Identities.lean — the parts of WP59 / the dark-matter monograph that CAN be
  machine-checked, stated for what they actually say.

  STATUS: UNTESTED until the Actions run says otherwise (Mathlib, Lean v4.32.0).

  WHAT IS PROVED:
   1. `eta_pow_neg_k`   : for η > 1 and x > 0,  η ^ (-(log x / log η)) = x⁻¹.
                          (η cancels completely.)
   2. `contact_profile` : x^β · η^(-k(x)) = x^(β-1).   (so the "Tribonacci-weighted"
                          profile is a plain power law with exponent β-1.)
   3. `factor_at_third` : the factor at x = 1/3 is exactly 3, not "2.3–2.8".
   4. `contact_profile_increasing` : for β > 1 (β = 3/2 in the paper) the contact profile
                          is strictly INCREASING outward.
   5. `tribonacci_exists` : a root of t³ = t² + t + 1 lies in (1.8392, 1.8393).
   6. `monograph_eta_not_root` : the constant 1.8390908052 used in the script and the
                          Lean file is NOT a root of t³ = t² + t + 1.

  WHAT IS NOT PROVED (and is not claimed): anything about lensing, convergence,
  magnification, clusters, CDM, or the Natarajan data. Nothing here supports T2, T3,
  F2 or F5; item 1–4 in fact show the profile is x^(β-1) and rises with radius.
-/

namespace Wp59

open Real

/-- η cancels: η^(-ln x / ln η) = 1/x for any η > 1. -/
theorem eta_pow_neg_k {η x : ℝ} (hη : 1 < η) (hx : 0 < x) :
    η ^ (-(Real.log x / Real.log η)) = x⁻¹ := by
  have hl : Real.log η ≠ 0 := (Real.log_pos hη).ne'
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hη)]
  have h : Real.log η * (-(Real.log x / Real.log η)) = -Real.log x := by
    field_simp <;> ring
  rw [h, Real.exp_neg, Real.exp_log hx]

/-- The "Tribonacci-weighted" profile is a plain power law of exponent β-1. -/
theorem contact_profile {η x : ℝ} (β : ℝ) (hη : 1 < η) (hx : 0 < x) :
    x ^ β * η ^ (-(Real.log x / Real.log η)) = x ^ (β - 1) := by
  rw [eta_pow_neg_k hη hx, Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]

/-- At x = 1/3 the factor is exactly 3. -/
theorem factor_at_third {η : ℝ} (hη : 1 < η) :
    η ^ (-(Real.log (1/3 : ℝ) / Real.log η)) = 3 := by
  rw [eta_pow_neg_k hη (by norm_num)]
  norm_num

/-- With β > 1 (the paper uses β = 3/2) the contact profile rises outward. -/
theorem contact_profile_increasing {η x y : ℝ} (β : ℝ) (hβ : 1 < β) (hη : 1 < η)
    (hx : 0 < x) (hxy : x < y) :
    x ^ β * η ^ (-(Real.log x / Real.log η)) <
      y ^ β * η ^ (-(Real.log y / Real.log η)) := by
  have hy : 0 < y := lt_trans hx hxy
  rw [contact_profile β hη hx, contact_profile β hη hy]
  exact Real.rpow_lt_rpow hx.le hxy (by linarith)

/-- A root of t³ = t² + t + 1 lies in (1.8392, 1.8393): the Tribonacci constant is
    ≈ 1.83929, not 1.83909. (Existence only; uniqueness is not claimed here.) -/
theorem tribonacci_exists :
    ∃ t : ℝ, (1.8392 : ℝ) < t ∧ t < 1.8393 ∧ t ^ 3 = t ^ 2 + t + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 3 - t ^ 2 - t - 1) (Set.Icc (1.8392 : ℝ) 1.8393) := by
    fun_prop
  have h0 : (1.8392 : ℝ) ^ 3 - (1.8392 : ℝ) ^ 2 - 1.8392 - 1 < 0 := by norm_num
  have h1 : (0 : ℝ) < (1.8393 : ℝ) ^ 3 - (1.8393 : ℝ) ^ 2 - 1.8393 - 1 := by norm_num
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 3 - t ^ 2 - t - 1) 1.8392)
      ((fun t : ℝ => t ^ 3 - t ^ 2 - t - 1) 1.8393) := ⟨h0, h1⟩
  obtain ⟨c, ⟨hc1, hc2⟩, hcz⟩ := intermediate_value_Ioo (by norm_num) hc hmem
  have hz : c ^ 3 - c ^ 2 - c - 1 = 0 := hcz
  exact ⟨c, hc1, hc2, by linarith⟩

/-- The value 1.8390908052 used in `dark_matter_simulation.py` and
    `DarkMatter_MachineVerified.lean` is not a root of t³ = t² + t + 1. -/
theorem monograph_eta_not_root :
    (1.8390908052 : ℝ) ^ 3 ≠ (1.8390908052 : ℝ) ^ 2 + 1.8390908052 + 1 := by
  norm_num

end Wp59

#print axioms Wp59.eta_pow_neg_k
#print axioms Wp59.contact_profile
#print axioms Wp59.factor_at_third
#print axioms Wp59.contact_profile_increasing
#print axioms Wp59.tribonacci_exists
#print axioms Wp59.monograph_eta_not_root
