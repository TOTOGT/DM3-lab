import Mathlib

/-!
# Prop 6.1, stage 3a: the final real-number arithmetic, in the variable u = n^(1/20)
UNTESTED, not compiled anywhere. Pure real arithmetic; no connection to counts yet.

With n = u^20 (so X = n^(1/4) = u^5, n^(1/5) = u^4, sqrt n = u^10, n^(-3/10) = u^(-6)) and a natural
P = floor(2X) with 2u^5 - 1 <= P <= 2u^5, the paper's chain (6.1) + (6.2) becomes the inequality of
`final_arith`.  The paper takes real P = 2X; using a natural P costs the factor 127/128 (P >= 127/64 u^5),
absorbed in the constants 128/(15*127) and 8192/16129 below.  Python (Fraction) says the value at
w = 4/9 is 0.6458 < 2/3 (slack 0.021) with E <= (49/50)/u^6; this is a re-derivation, not the paper's 21235493/33177600.
-/

namespace Section63

theorem numeric_core (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 4 / 9) :
    21 / 50 + (49 / 50) * (4 / 15 * w + w ^ 6)
      + (44 / 15) * (128 / (15 * 127) * w + 8192 / 16129 * w ^ 6 + 2 / 15 * w ^ 6 + w ^ 16)
    < 2 / 3 := by
  have h6 : w ^ 6 ≤ (4 / 9) ^ 6 := pow_le_pow_left₀ hw0.le hw 6
  have h16 : w ^ 16 ≤ (4 / 9) ^ 16 := pow_le_pow_left₀ hw0.le hw 16
  first
    | linarith
    | (norm_num at h6 h16 ⊢; linarith)
    | nlinarith [h6, h16, hw, hw0]

theorem final_arith (u P E : ℝ) (hu : 0 < u) (hX : 64 ≤ u ^ 5)
    (hP1 : 2 * u ^ 5 - 1 ≤ P) (hP2 : P ≤ 2 * u ^ 5)
    (hE0 : 0 ≤ E) (hE : E ≤ (49 / 50) / u ^ 6) :
    21 / 50 + E * (2 * P / 15 + 1)
      + (4 / 3) * ((11 / 5) * u ^ 4)
          * (2 / (15 * P) + 2 / P ^ 2 + (2 * u ^ 10 / 15 + 1) / u ^ 20)
    < 2 / 3 := by
  have hu94 : 9 / 4 ≤ u := by
    by_contra h
    push_neg at h
    have h1 : u ^ 5 < (9 / 4 : ℝ) ^ 5 := pow_lt_pow_left₀ h hu.le (by norm_num)
    norm_num at h1
    linarith
  have hw0 : 0 < 1 / u := by positivity
  have hw : 1 / u ≤ 4 / 9 := by
    rw [div_le_div_iff₀ hu (by norm_num)]
    linarith
  have hPlow : (127 / 64 : ℝ) * u ^ 5 ≤ P := by linarith
  have hPpos : 0 < P := by
    have : (0 : ℝ) < u ^ 5 := by positivity
    linarith
  have hu5 : (0 : ℝ) < u ^ 5 := by positivity
  -- small-prime side
  have hT1a : E * (2 * P / 15 + 1) ≤ ((49 / 50) / u ^ 6) * (4 * u ^ 5 / 15 + 1) :=
    mul_le_mul hE (by linarith) (by linarith) (by positivity)
  have hT1b : ((49 / 50) / u ^ 6) * (4 * u ^ 5 / 15 + 1)
      = (49 / 50) * (4 / 15 * (1 / u) + (1 / u) ^ 6) := by
    field_simp
    try ring
  -- large-prime side
  have e2 : 2 / (15 * P) ≤ (128 / (15 * 127)) / u ^ 5 := by
    rw [div_le_div_iff₀ (by positivity) hu5]
    linarith
  have hPsq : ((127 / 64 : ℝ) * u ^ 5) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by positivity) hPlow 2
  have e3 : 2 / P ^ 2 ≤ (8192 / 16129) / u ^ 10 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hPsq]
  have hB : (4 / 3) * ((11 / 5) * u ^ 4)
          * (2 / (15 * P) + 2 / P ^ 2 + (2 * u ^ 10 / 15 + 1) / u ^ 20)
      ≤ (44 / 15) * (128 / (15 * 127) * (1 / u) + 8192 / 16129 * (1 / u) ^ 6
          + 2 / 15 * (1 / u) ^ 6 + (1 / u) ^ 16) := by
    calc (4 / 3) * ((11 / 5) * u ^ 4)
          * (2 / (15 * P) + 2 / P ^ 2 + (2 * u ^ 10 / 15 + 1) / u ^ 20)
        ≤ (4 / 3) * ((11 / 5) * u ^ 4)
          * ((128 / (15 * 127)) / u ^ 5 + (8192 / 16129) / u ^ 10
              + (2 * u ^ 10 / 15 + 1) / u ^ 20) :=
          mul_le_mul_of_nonneg_left (add_le_add (add_le_add e2 e3) le_rfl) (by positivity)
      _ = (44 / 15) * (128 / (15 * 127) * (1 / u) + 8192 / 16129 * (1 / u) ^ 6
          + 2 / 15 * (1 / u) ^ 6 + (1 / u) ^ 16) := by
          field_simp
          try ring
  have hnum := numeric_core (1 / u) hw0 hw
  linarith [hT1a, hT1b, hB, hnum]

end Section63

#print axioms Section63.numeric_core
#print axioms Section63.final_arith
