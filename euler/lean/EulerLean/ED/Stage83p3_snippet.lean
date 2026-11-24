/-! # Prime-3 improvement, arithmetic lemmas  (UNTESTED: not compiled anywhere)

SNIPPET, to be appended to Stage83cut.lean (after `Section5.five_four` and after
`Section63.numeric_core` respectively), or placed in a new file importing Stage83cut.
Nothing here depends on the prime-3 formula: both are pure arithmetic.
The prime-3 identity itself (3B = 8σ + 16 cEis) is NOT used and NOT proved here.

Hand check (exact rationals, Python Fraction, not Lean):
  five_four_gt3: Σ_{p∈{7,11,19,23,31,43,47,59}} 1/(p(p-1)) + (60/59)(2/900+2/3600)
                 = 0.0430093 < 13/300 = 0.0433333, margin 1051941970241/3246330174110100.
  numeric_core_p3 at w = 4/9: value 0.663429044... < 2/3, slack 0.0032376.
-/

namespace Section5

lemma small_sum_gt3 :
    ∑ p ∈ ({7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      < 13 / 300 - (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) := by
  norm_num [Finset.sum_insert]

/-- (5.4) with the prime 3 removed: 2 Σ_{p ≡ 3 (4), p > 3} 1/(p(p−1)) < 13/150. -/
theorem five_four_gt3 (K : ℕ) :
    2 * ∑ p ∈ (PT K).filter (fun p => 3 < p), 1 / ((p : ℝ) * ((p : ℝ) - 1)) < 13 / 150 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not ((PT K).filter (fun p => 3 < p))
    (fun p => p ≤ 60) (fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1)))
  -- primes 3 < p ≤ 60
  have hsmall : ∑ p ∈ ((PT K).filter (fun p => 3 < p)).filter (fun p => p ≤ 60),
        1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ ({7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ), 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [PT, Finset.mem_filter] at hp
      obtain ⟨⟨⟨_, hpr, h4⟩, h3⟩, hle⟩ := hp
      have h9 := small_primes p hle hpr h4
      simp only [Finset.mem_insert, Finset.mem_singleton] at h9 ⊢
      omega
    · intro p hp _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  -- primes above 60 (identical to five_four)
  have hlarge : ∑ p ∈ ((PT K).filter (fun p => 3 < p)).filter (fun p => ¬ p ≤ 60),
        1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) := by
    have hsub : ((PT K).filter (fun p => 3 < p)).filter (fun p => ¬ p ≤ 60)
        ⊆ (Finset.Ioc 60 K).filter (fun p => p.Prime ∧ p % 4 = 3) := by
      intro p hp
      simp only [PT, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨⟨⟨hr, hpr, h4⟩, h3⟩, hle⟩ := hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, by omega⟩, hpr, h4⟩
    have hterm : ∀ p ∈ ((PT K).filter (fun p => 3 < p)).filter (fun p => ¬ p ≤ 60),
        1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (60 / 59) * (1 / (p : ℝ) ^ 2) := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      have hp61 : (61 : ℝ) ≤ p := by exact_mod_cast (show 61 ≤ p by omega)
      have hpos : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      rw [div_le_iff₀ hpos]
      have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      have : (60 / 59 : ℝ) * (1 / (p : ℝ) ^ 2) * ((p : ℝ) * ((p : ℝ) - 1))
          = (60 / 59) * (((p : ℝ) - 1) / p) := by
        field_simp
      rw [this]
      have hq : (59 / 60 : ℝ) ≤ ((p : ℝ) - 1) / p := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have h1 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ p ∈ ((PT K).filter (fun p => 3 < p)).filter (fun p => ¬ p ≤ 60), 1 / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (Finset.Ioc 60 K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h3 := prime_tail 60 (by norm_num) K
    push_cast at h3
    have h4 : (60 / 59 : ℝ) * ∑ p ∈ ((PT K).filter (fun p => 3 < p)).filter (fun p => ¬ p ≤ 60),
          1 / (p : ℝ) ^ 2
        ≤ (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) (by norm_num)
    linarith
  have := small_sum_gt3
  linarith

end Section5

namespace Section63

/-- numeric_core with the prime-3 term replaced: 21/50 → 139/450 (= 21/50 − 1/9),
    small-prime error doubled (K = 2), prime-3 error (2/3)·(49/50)·w⁶ = (49/75) w⁶. -/
theorem numeric_core_p3 (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 4 / 9) :
    139 / 450 + 2 * ((49 / 50) * (4 / 15 * w + w ^ 6)) + (49 / 75) * w ^ 6
      + (44 / 15) * (128 / (15 * 127) * w + 8192 / 16129 * w ^ 6 + 2 / 15 * w ^ 6 + w ^ 16)
    < 2 / 3 := by
  have h6 : w ^ 6 ≤ (4 / 9) ^ 6 := pow_le_pow_left₀ hw0.le hw 6
  have h16 : w ^ 16 ≤ (4 / 9) ^ 16 := pow_le_pow_left₀ hw0.le hw 16
  first
    | linarith
    | (norm_num at h6 h16 ⊢; linarith)
    | nlinarith [h6, h16, hw, hw0]

end Section63

-- after appending to Stage83cut.lean, also run:
-- #print axioms Section5.five_four_gt3
-- #print axioms Section63.numeric_core_p3
