import Mathlib

/-!
UNTESTED. Not compiled anywhere. Finite algebra only:
the one-vector quadratic-form bound  <h,Th> <= B ||h||^2,  h = f - mu*1,
implies the pointwise bound (3.8):  (T f)(y0) <= sigma*mu + B*(1-mu).
The quadratic-form bound itself is an explicit HYPOTHESIS (hquad); nothing here
proves it. f is the indicator of O, given through hf.
-/

namespace EulerBridge

theorem pointwise_of_quadform
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (T : (Y → ℝ) →ₗ[ℝ] (Y → ℝ)) (σ B μ : ℝ)
    (O : Finset Y) (y₀ : Y) (hy₀ : y₀ ∈ O)
    (f : Y → ℝ) (hf : ∀ y, f y = if y ∈ O then (1 : ℝ) else 0)
    (hT1 : T (fun _ => (1 : ℝ)) = fun _ => σ)
    (hsa : ∀ u v : Y → ℝ, ∑ y, u y * T v y = ∑ y, T u y * v y)
    (hconst : ∀ y ∈ O, T f y = T f y₀)
    (hμ : μ * (Fintype.card Y : ℝ) = (O.card : ℝ))
    (hquad : ∑ y, (f y - μ) * T (fun z => f z - μ) y
               ≤ B * ∑ y, (f y - μ) ^ 2) :
    T f y₀ ≤ σ * μ + B * (1 - μ) := by
  have hS : (0 : ℝ) < (O.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨y₀, hy₀⟩
  -- sum of the indicator
  have F1 : ∑ y, f y = (O.card : ℝ) := by
    calc ∑ y, f y = ∑ y, (if y ∈ O then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun y _ => hf y)
      _ = (O.card : ℝ) := by simp
  have hsq : ∀ y, f y ^ 2 = f y := by
    intro y; rw [hf y]; split_ifs <;> norm_num
  have F2 : ∑ y, f y ^ 2 = (O.card : ℝ) := by
    rw [← F1]; exact Finset.sum_congr rfl (fun y _ => hsq y)
  -- sum of T f  (uses T 1 = sigma and self-adjointness)
  have F3 : ∑ y, T f y = σ * (O.card : ℝ) := by
    have h : ∑ y, (1 : ℝ) * T f y = ∑ y, T (fun _ => (1 : ℝ)) y * f y :=
      hsa (fun _ => (1 : ℝ)) f
    have e1 : ∑ y, T f y = ∑ y, (1 : ℝ) * T f y := by simp
    have e2 : ∑ y, T (fun _ => (1 : ℝ)) y * f y = σ * ∑ y, f y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by rw [hT1])
    rw [e1, h, e2, F1]
  -- <f, T f> = |O| * (T f)(y0), from constancy of T f on O
  have F4 : ∑ y, f y * T f y = (O.card : ℝ) * T f y₀ := by
    calc ∑ y, f y * T f y = ∑ y, (if y ∈ O then T f y else 0) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hf y]; split_ifs <;> simp
      _ = ∑ y ∈ O, T f y := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ y ∈ O, T f y₀ := Finset.sum_congr rfl hconst
      _ = (O.card : ℝ) * T f y₀ := by simp
  -- T (f - mu*1) = T f - mu*sigma
  have hh : (fun z => f z - μ) = f - μ • (fun _ : Y => (1 : ℝ)) := by
    ext z; simp
  have Th : ∀ y, T (fun z => f z - μ) y = T f y - μ * σ := by
    intro y
    rw [hh, map_sub, map_smul, hT1]
    simp
  -- identity 1:  <h, T h> expanded
  have m1 : ∑ y, μ * σ * f y = μ * σ * ∑ y, f y := by rw [Finset.mul_sum]
  have m2 : ∑ y, μ * T f y = μ * ∑ y, T f y := by rw [Finset.mul_sum]
  have hexp : ∑ y, (f y - μ) * (T f y - μ * σ)
      = ∑ y, f y * T f y - μ * σ * ∑ y, f y - μ * ∑ y, T f y
        + μ * μ * σ * (Fintype.card Y : ℝ) := by
    have e : ∀ y, (f y - μ) * (T f y - μ * σ)
        = f y * T f y - μ * σ * f y - μ * T f y + μ * μ * σ := by
      intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, m1, m2]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- identity 2:  <h, h> expanded
  have m3 : ∑ y, 2 * μ * f y = 2 * μ * ∑ y, f y := by rw [Finset.mul_sum]
  have hexp2 : ∑ y, (f y - μ) ^ 2
      = ∑ y, f y ^ 2 - 2 * μ * ∑ y, f y + μ ^ 2 * (Fintype.card Y : ℝ) := by
    have e : ∀ y, (f y - μ) ^ 2 = f y ^ 2 - 2 * μ * f y + μ ^ 2 := by
      intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, m3]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- use mu * |Y| = |O|
  have hμ2 : μ * μ * σ * (Fintype.card Y : ℝ) = μ * σ * (O.card : ℝ) := by
    rw [← hμ]; ring
  have hμ3 : μ ^ 2 * (Fintype.card Y : ℝ) = μ * (O.card : ℝ) := by
    rw [← hμ]; ring
  have hBμ : B * (μ ^ 2 * (Fintype.card Y : ℝ)) = B * (μ * (O.card : ℝ)) := by
    rw [hμ3]
  simp only [Th] at hquad
  rw [hexp, hexp2, F4, F1, F2, F3] at hquad
  -- hquad:  S*t - 2*mu*sigma*S + mu^2*sigma*|Y|  <=  B*(S - 2*mu*S + mu^2*|Y|)
  -- i.e.    S*(t - sigma*mu)  <=  B*S*(1-mu).  Cancel S > 0.
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < (O.card : ℝ) * (T f y₀ - (σ * μ + B * (1 - μ))) :=
    mul_pos hS (sub_pos.2 hlt)
  nlinarith [hquad, hμ2, hμ3, hBμ, hpos]

#print axioms EulerBridge.pointwise_of_quadform

end EulerBridge
