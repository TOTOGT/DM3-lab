import Mathlib

/-!
# ChebMajorant_isolated.lean   (ISOLATED; UNTESTED: not compiled when written)

Pure scalar mathematics, `import Mathlib` only; no project import, no axioms, no stubs, no production edit.
Sections 0 and 1 are copied VERBATIM (by script) from `euler/StageA4l.lean` (definitions `w`, `u`, lemmas
`w_sin ... w_abs_le`, `u_eq`), so that the new statements are about the very same objects that
`S_norm_le` uses.  Everything under "NEW" is untested.

NEW:  for real X ≥ 1 and |t| ≤ X :   |w t k| ≤ w X k      (w = Chebyshev U_k in the variable c, w_1 = 2c)
      and the transport lemma     |μ| ≤ 2 X √l  ⟹  |u l μ k| ≤ √l^k · w X k.
Specialisation X = 51/50 is the last theorem.  Run:   lake env lean EulerLean/ED/ChebMajorant_isolated.lean
-/

namespace ChebMajorant

/-! ## 0. verbatim from StageA4l.lean: w and its interior bound -/

/-- Chebyshev-type recurrence w_0 = 1, w_1 = 2c, w_{k+2} = 2c w_{k+1} - w_k. -/
def w (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * c
  | (k + 2) => 2 * c * w c (k + 1) - w c k

theorem w_sin (θ : ℝ) (k : ℕ) :
    w (Real.cos θ) k * Real.sin θ = Real.sin ((k + 1) * θ) ∧
    w (Real.cos θ) (k + 1) * Real.sin θ = Real.sin ((k + 2) * θ) := by
  induction k with
  | zero =>
    refine ⟨by simp [w], ?_⟩
    simp only [w]; push_cast
    rw [show ((0:ℝ) + 2) * θ = θ + θ by ring, Real.sin_add]; ring
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by push_cast; rw [h2]; ring_nf, ?_⟩
    have e : w (Real.cos θ) (k + 2) * Real.sin θ = Real.sin (((k + 1 : ℕ) + 2 : ℝ) * θ) := by
      show (2 * Real.cos θ * w (Real.cos θ) (k + 1) - w (Real.cos θ) k) * Real.sin θ = _
      have a1 : Real.sin (((k : ℝ) + 3) * θ) = Real.sin (((k : ℝ) + 2) * θ) * Real.cos θ
          + Real.cos (((k : ℝ) + 2) * θ) * Real.sin θ := by
        rw [← Real.sin_add]; ring_nf
      have a2 : Real.sin (((k : ℝ) + 1) * θ) = Real.sin (((k : ℝ) + 2) * θ) * Real.cos θ
          - Real.cos (((k : ℝ) + 2) * θ) * Real.sin θ := by
        rw [← Real.sin_sub]; ring_nf
      have : (2 * Real.cos θ * w (Real.cos θ) (k + 1) - w (Real.cos θ) k) * Real.sin θ
          = 2 * Real.cos θ * (w (Real.cos θ) (k + 1) * Real.sin θ) - w (Real.cos θ) k * Real.sin θ := by ring
      rw [this, h1, h2]
      push_cast
      rw [show (((k : ℝ) + 1 + 2) * θ) = ((k : ℝ) + 3) * θ by ring, a1]
      nlinarith [a2]
    exact e

theorem abs_sin_nat_mul_le (θ : ℝ) (n : ℕ) : |Real.sin ((n : ℝ) * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : Real.sin (((n + 1 : ℕ) : ℝ) * θ) = Real.sin ((n : ℝ) * θ) * Real.cos θ
        + Real.cos ((n : ℝ) * θ) * Real.sin θ := by
      rw [← Real.sin_add]; push_cast; ring_nf
    rw [this]
    calc _ ≤ |Real.sin ((n : ℝ) * θ) * Real.cos θ| + |Real.cos ((n : ℝ) * θ) * Real.sin θ| := abs_add_le _ _
      _ ≤ |Real.sin ((n : ℝ) * θ)| * 1 + 1 * |Real.sin θ| := by
        rw [abs_mul, abs_mul]
        gcongr
        · exact Real.abs_cos_le_one _
        · exact Real.abs_cos_le_one _
      _ ≤ n * |Real.sin θ| + 1 * |Real.sin θ| := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * |Real.sin θ| := by push_cast; ring

theorem w_abs_le_interior (c : ℝ) (hc : |c| < 1) (k : ℕ) : |w c k| ≤ k + 1 := by
  have h1 : -1 ≤ c := by linarith [abs_lt.1 hc |>.1]
  have h2 : c ≤ 1 := by linarith [abs_lt.1 hc |>.2]
  set θ := Real.arccos c with hθ
  have hcos : Real.cos θ = c := Real.cos_arccos h1 h2
  have hsin : 0 < Real.sin θ := by
    rw [hθ, Real.sin_arccos]
    apply Real.sqrt_pos.2
    nlinarith [abs_lt.1 hc, sq_abs c, abs_nonneg c]
  have := (w_sin θ k).1
  rw [hcos] at this
  have hb := abs_sin_nat_mul_le θ (k + 1)
  push_cast at hb
  rw [← this, abs_mul, abs_of_pos hsin] at hb
  have : |w c k| * Real.sin θ ≤ ((k : ℝ) + 1) * Real.sin θ := by
    simpa [abs_of_pos hsin] using hb
  exact le_of_mul_le_mul_right this hsin

theorem w_pm (c : ℝ) (hc : c ^ 2 = 1) (k : ℕ) : w c k = c ^ k * (k + 1) ∧ w c (k + 1) = c ^ (k + 1) * (k + 2) := by
  induction k with
  | zero => refine ⟨by simp [w], by simp [w]; ring⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by push_cast; rw [h2]; ring, ?_⟩
    show 2 * c * w c (k + 1) - w c k = _
    rw [h1, h2]
    have : c ^ (k + 2) = c ^ k * c ^ 2 := by ring
    have h3 : c ^ (k + 1 + 1) * (((k + 1 : ℕ) : ℝ) + 2) = c ^ k * c ^ 2 * ((k : ℝ) + 3) := by
      push_cast; rw [← this]; ring
    rw [h3, hc]
    have h4 : c ^ (k + 1) = c ^ k * c := by ring
    rw [h4]
    have h5 : 2 * c * (c ^ k * c * ((k : ℝ) + 2)) = 2 * c ^ k * (c ^ 2) * ((k : ℝ) + 2) := by ring
    rw [h5, hc]; ring

theorem w_abs_le (c : ℝ) (hc : |c| ≤ 1) (k : ℕ) : |w c k| ≤ k + 1 := by
  rcases lt_or_eq_of_le hc with h | h
  · exact w_abs_le_interior c h k
  · have hc2 : c ^ 2 = 1 := by rw [← sq_abs, h]; norm_num
    rw [(w_pm c hc2 k).1, abs_mul, abs_pow, h]
    simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1)]



/-! ## 1. verbatim from StageA4l.lean: u and u_eq -/

/-- scalar form of the prime-power recurrence: u_0 = 1, u_1 = x, u_{k+2} = x u_{k+1} - l u_k -/
def u (l x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x
  | (k + 2) => x * u l x (k + 1) - l * u l x k

theorem u_eq (l : ℝ) (hl : 0 < l) (x : ℝ) (k : ℕ) :
    u l x k = Real.sqrt l ^ k * w (x / (2 * Real.sqrt l)) k ∧
    u l x (k + 1) = Real.sqrt l ^ (k + 1) * w (x / (2 * Real.sqrt l)) (k + 1) := by
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hs2 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
  have hx : x = 2 * Real.sqrt l * (x / (2 * Real.sqrt l)) := by field_simp
  induction k with
  | zero => refine ⟨by simp [u, w], ?_⟩; simp only [u, w]; rw [pow_one]; field_simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show x * u l x (k + 1) - l * u l x k = _
    rw [h1, h2]
    show _ = Real.sqrt l ^ (k + 1 + 1) * (2 * (x / (2 * Real.sqrt l)) * w (x / (2 * Real.sqrt l)) (k + 1)
        - w (x / (2 * Real.sqrt l)) k)
    set c := x / (2 * Real.sqrt l)
    linear_combination (Real.sqrt l ^ (k + 1) * w c (k + 1)) * hx - (Real.sqrt l ^ k * w c k) * hs2.symm


/-! ## 2. NEW: positivity and monotonicity of U_k on [1, ∞) -/

/-- w t k ≥ 0 and nondecreasing in k, for t ≥ 1 -/
theorem w_nonneg_mono {t : ℝ} (ht : 1 ≤ t) :
    ∀ k : ℕ, 0 ≤ w t k ∧ w t k ≤ w t (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp only [w]
    constructor <;> linarith
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hk1 : 0 ≤ w t (k + 1) := le_trans h0 h1
    constructor
    · exact hk1
    · show w t (k + 1) ≤ 2 * t * w t (k + 1) - w t k
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t - 2) hk1]

/-- D_k = w x k - w t k satisfies 0 ≤ D_k ≤ D_{k+1} for 1 ≤ t ≤ x.
The step is the identity
D_{k+2} - D_{k+1} = (2x-2) D_{k+1} + (D_{k+1} - D_k) + 2 (x-t) w t (k+1). -/
theorem w_sub_mono {t x : ℝ} (ht : 1 ≤ t) (htx : t ≤ x) :
    ∀ k : ℕ, 0 ≤ w x k - w t k ∧ w x k - w t k ≤ w x (k + 1) - w t (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp only [w]
    constructor <;> linarith
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hD1 : 0 ≤ w x (k + 1) - w t (k + 1) := le_trans h0 h1
    have hp : 0 ≤ w t (k + 1) := (w_nonneg_mono ht (k + 1)).1
    constructor
    · exact hD1
    · show w x (k + 1) - w t (k + 1)
          ≤ (2 * x * w x (k + 1) - w x k) - (2 * t * w t (k + 1) - w t k)
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * x - 2) hD1,
                 mul_nonneg (by linarith : (0 : ℝ) ≤ x - t) hp]

/-- U_k(1) = k + 1 -/
theorem w_one : ∀ k : ℕ, w 1 k = (k : ℝ) + 1 ∧ w 1 (k + 1) = (k : ℝ) + 2 := by
  intro k
  induction k with
  | zero => constructor <;> norm_num [w]
  | succ k ih =>
    obtain ⟨a, b⟩ := ih
    refine ⟨by push_cast; rw [b]; ring, ?_⟩
    show 2 * 1 * w 1 (k + 1) - w 1 k = ((k + 1 : ℕ) : ℝ) + 2
    rw [b, a]; push_cast; ring

/-- parity: U_k(-c) = (-1)^k U_k(c) -/
theorem w_neg (c : ℝ) : ∀ k : ℕ,
    w (-c) k = (-1) ^ k * w c k ∧ w (-c) (k + 1) = (-1) ^ (k + 1) * w c (k + 1) := by
  intro k
  induction k with
  | zero => constructor <;> simp [w]
  | succ k ih =>
    obtain ⟨a, b⟩ := ih
    refine ⟨b, ?_⟩
    show 2 * (-c) * w (-c) (k + 1) - w (-c) k
        = (-1) ^ (k + 1 + 1) * (2 * c * w c (k + 1) - w c k)
    rw [a, b]; ring

/-! ## 3. NEW: the majorant theorem -/

/-- For X ≥ 1 and |t| ≤ X:  |U_k(t)| ≤ U_k(X). -/
theorem w_abs_le_w {X t : ℝ} (hX : 1 ≤ X) (ht : |t| ≤ X) (k : ℕ) : |w t k| ≤ w X k := by
  by_cases h1 : |t| ≤ 1
  · have a := w_abs_le t h1 k
    have b := (w_one k).1
    have c := (w_sub_mono (le_refl (1 : ℝ)) hX k).1
    linarith
  · push_neg at h1
    have hs : (1 : ℝ) ≤ |t| := h1.le
    have hmono := (w_sub_mono hs ht k).1
    have hnn := (w_nonneg_mono hs k).1
    have habs : |w t k| = w (|t|) k := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h] at hnn ⊢
        exact abs_of_nonneg hnn
      · have ht' : t = -|t| := by linarith
        have hp := (w_neg (|t|) k).1
        rw [← ht'] at hp
        rw [hp, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hnn]
    rw [habs]
    linarith

/-- transport to the operator recurrence u (the scalar that `S_norm_le` consumes) -/
theorem u_abs_le_cheb (l : ℝ) (hl : 0 < l) (X : ℝ) (hX : 1 ≤ X) (μ : ℝ)
    (hμ : |μ| ≤ 2 * X * Real.sqrt l) (k : ℕ) :
    |u l μ k| ≤ Real.sqrt l ^ k * w X k := by
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hc : |μ / (2 * Real.sqrt l)| ≤ X := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt l), div_le_iff₀ (by positivity)]
    exact le_of_le_of_eq hμ (by ring)
  rw [(u_eq l hl μ k).1, abs_mul, abs_pow, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left (w_abs_le_w hX hc k) (by positivity)

/-- the case used by the 2.04 route: 2X = 51/25 -/
theorem u_abs_le_cheb_51_50 (l : ℝ) (hl : 0 < l) (μ : ℝ)
    (hμ : |μ| ≤ (51 / 25) * Real.sqrt l) (k : ℕ) :
    |u l μ k| ≤ Real.sqrt l ^ k * w (51 / 50) k :=
  u_abs_le_cheb l hl (51 / 50) (by norm_num) μ (by linarith) k

/-- the original Ramanujan case X = 1 is recovered (w 1 k = k+1) -/
theorem u_abs_le_cheb_one (l : ℝ) (hl : 0 < l) (μ : ℝ)
    (hμ : |μ| ≤ 2 * Real.sqrt l) (k : ℕ) :
    |u l μ k| ≤ ((k : ℝ) + 1) * Real.sqrt l ^ k := by
  have := u_abs_le_cheb l hl 1 le_rfl μ (by linarith) k
  rw [(w_one k).1] at this
  linarith [mul_comm (Real.sqrt l ^ k) ((k : ℝ) + 1)]

end ChebMajorant

#print axioms ChebMajorant.w_abs_le_w
#print axioms ChebMajorant.u_abs_le_cheb
#print axioms ChebMajorant.u_abs_le_cheb_51_50
#print axioms ChebMajorant.u_abs_le_cheb_one
