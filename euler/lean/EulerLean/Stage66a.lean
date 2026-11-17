import Mathlib

/-! # Stage66a: first part of hr2, representations as a sum of two squares  (UNTESTED when written)

Goal of the whole stage 66 series (NOT done here): card {(a,b) in Z^2 : a^2+b^2 = u} <= 4 * Mq u.
This file proves only the two easy reductions, elementary and pair-level (no Gaussian integers):
  * inert_le : p prime = 3 mod 4, p | u  =>  |S u| <= |S (u / p^2)|
  * two_le   : 2 | u                     =>  |S u| <= |S (u / 2)|
  * S1_card  : |S 1| = 4
It does NOT treat primes q = 1 mod 4 (that is the splitting step, stage 66b) and it does not mention Mq,
Section42.R2 or Mn. Nothing here is hr2. -/

namespace TwoSq

noncomputable def S (u : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(u : ℤ)) u) ×ˢ (Finset.Icc (-(u : ℤ)) u)).filter
    (fun q => q.1 ^ 2 + q.2 ^ 2 = (u : ℤ))

lemma le_sq' (b : ℤ) : b ≤ b ^ 2 := by
  rcases le_or_gt b 0 with h | h
  · nlinarith [sq_nonneg b]
  · nlinarith [mul_nonneg h.le (by linarith : (0 : ℤ) ≤ b - 1)]

lemma mem_S (u : ℕ) (q : ℤ × ℤ) : q ∈ S u ↔ q.1 ^ 2 + q.2 ^ 2 = (u : ℤ) := by
  unfold S
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    have h1 := le_sq' q.1
    have h2 := le_sq' (-q.1)
    have h3 := le_sq' q.2
    have h4 := le_sq' (-q.2)
    have e1 : (-q.1) ^ 2 = q.1 ^ 2 := by ring
    have e2 : (-q.2) ^ 2 = q.2 ^ 2 := by ring
    have s1 := sq_nonneg q.1
    have s2 := sq_nonneg q.2
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, h⟩

/-- a prime = 3 mod 4 dividing a sum of two squares divides both (same proof as Sufficiency.dvd_of_sq_add) -/
lemma dvd_of_sq_add {q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3) (x y : ℤ)
    (h : (q : ℤ) ∣ x ^ 2 + y ^ 2) : (q : ℤ) ∣ x ∧ (q : ℤ) ∣ y := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h0 : ((x : ZMod q)) ^ 2 + (y : ZMod q) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 2 + y ^ 2) q).2 h
    push_cast at this
    exact this
  by_cases hy : (y : ZMod q) = 0
  · have hx2 : (x : ZMod q) ^ 2 = 0 := by rw [hy] at h0; simpa using h0
    have hx : (x : ZMod q) = 0 := pow_eq_zero_iff (by norm_num) |>.1 hx2
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x q).1 hx,
           (ZMod.intCast_zmod_eq_zero_iff_dvd y q).1 hy⟩
  · exfalso
    have hxy : (x : ZMod q) ^ 2 = -(y : ZMod q) ^ 2 := by linear_combination h0
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy hxy h3

lemma inert_dvd {p u : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpu : p ∣ u) {z : ℤ × ℤ}
    (hz : z ∈ S u) : (p : ℤ) ∣ z.1 ∧ (p : ℤ) ∣ z.2 := by
  apply dvd_of_sq_add hp h3
  rw [(mem_S u z).1 hz]
  exact_mod_cast hpu

theorem inert_le {p u : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpu : p ∣ u) :
    (S u).card ≤ (S (u / p ^ 2)).card := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := pow_pos (by exact_mod_cast hp.pos) 2
  by_cases hsq : p ^ 2 ∣ u
  · obtain ⟨t, ht⟩ := hsq
    have hdiv : u / p ^ 2 = t := by
      rw [ht]; exact Nat.mul_div_cancel_left t (pow_pos hp.pos 2)
    rw [hdiv]
    have hu : (u : ℤ) = (p : ℤ) ^ 2 * t := by rw [ht]; push_cast; ring
    refine Finset.card_le_card_of_injOn (fun z : ℤ × ℤ => (z.1 / p, z.2 / p)) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe] at hz ⊢
      rw [mem_S]
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inert_dvd hp h3 hpu hz
      have hs := (mem_S u z).1 hz
      have e1 : z.1 / p = a := by rw [ha]; exact Int.mul_ediv_cancel_left a hp0
      have e2 : z.2 / p = b := by rw [hb]; exact Int.mul_ediv_cancel_left b hp0
      rw [ha, hb] at hs
      show (z.1 / p) ^ 2 + (z.2 / p) ^ 2 = (t : ℤ)
      rw [e1, e2]
      have hm : (p : ℤ) ^ 2 * (a ^ 2 + b ^ 2) = (p : ℤ) ^ 2 * t := by linarith
      exact mul_left_cancel₀ hp2.ne' hm
    · intro z hz w hw hzw
      rw [Finset.mem_coe] at hz hw
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inert_dvd hp h3 hpu hz
      obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := inert_dvd hp h3 hpu hw
      simp only [Prod.mk.injEq] at hzw
      have e1 : z.1 / p = a := by rw [ha]; exact Int.mul_ediv_cancel_left a hp0
      have e2 : z.2 / p = b := by rw [hb]; exact Int.mul_ediv_cancel_left b hp0
      have e3 : w.1 / p = c := by rw [hc]; exact Int.mul_ediv_cancel_left c hp0
      have e4 : w.2 / p = d := by rw [hd]; exact Int.mul_ediv_cancel_left d hp0
      have hac : a = c := by rw [← e1, ← e3]; exact hzw.1
      have hbd : b = d := by rw [← e2, ← e4]; exact hzw.2
      exact Prod.ext (by rw [ha, hc, hac]) (by rw [hb, hd, hbd])
  · rcases (S u).eq_empty_or_nonempty with h | ⟨z, hz⟩
    · rw [h]; simp
    · exfalso
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inert_dvd hp h3 hpu hz
      have hs := (mem_S u z).1 hz
      rw [ha, hb] at hs
      have hd : ((p ^ 2 : ℕ) : ℤ) ∣ (u : ℤ) := ⟨a ^ 2 + b ^ 2, by push_cast; linarith⟩
      exact hsq (Int.natCast_dvd_natCast.1 hd)

theorem two_le {u : ℕ} (hu : 2 ∣ u) : (S u).card ≤ (S (u / 2)).card := by
  obtain ⟨t, ht⟩ := hu
  have hdiv : u / 2 = t := by omega
  rw [hdiv]
  have hut : (u : ℤ) = 2 * t := by exact_mod_cast ht
  have hev : ∀ z ∈ S u, (2 : ℤ) ∣ z.1 + z.2 := by
    intro z hz
    have hs := (mem_S u z).1 hz
    obtain ⟨r1, hr1⟩ := Int.even_mul_pred_self z.1
    obtain ⟨r2, hr2⟩ := Int.even_mul_pred_self z.2
    exact ⟨t - r1 - r2, by linarith⟩
  refine Finset.card_le_card_of_injOn
    (fun z : ℤ × ℤ => ((z.1 + z.2) / 2, (z.2 - z.1) / 2)) ?_ ?_
  · intro z hz
    rw [Finset.mem_coe] at hz ⊢
    rw [mem_S]
    obtain ⟨k, hk⟩ := hev z hz
    have hk2 : z.2 - z.1 = 2 * (k - z.1) := by linarith
    have e1 : (z.1 + z.2) / 2 = k := by rw [hk]; omega
    have e2 : (z.2 - z.1) / 2 = k - z.1 := by rw [hk2]; omega
    have hs := (mem_S u z).1 hz
    have hb : z.2 = 2 * k - z.1 := by linarith
    rw [hb] at hs
    show ((z.1 + z.2) / 2) ^ 2 + ((z.2 - z.1) / 2) ^ 2 = (t : ℤ)
    rw [e1, e2]
    linarith
  · intro z hz w hw hzw
    rw [Finset.mem_coe] at hz hw
    simp only [Prod.mk.injEq] at hzw
    obtain ⟨k, hk⟩ := hev z hz
    obtain ⟨l, hl⟩ := hev w hw
    have hk2 : z.2 - z.1 = 2 * (k - z.1) := by linarith
    have hl2 : w.2 - w.1 = 2 * (l - w.1) := by linarith
    have e1 : (z.1 + z.2) / 2 = k := by rw [hk]; omega
    have e2 : (z.2 - z.1) / 2 = k - z.1 := by rw [hk2]; omega
    have e3 : (w.1 + w.2) / 2 = l := by rw [hl]; omega
    have e4 : (w.2 - w.1) / 2 = l - w.1 := by rw [hl2]; omega
    have hkl : k = l := by rw [← e1, ← e3]; exact hzw.1
    have hzw2 : k - z.1 = l - w.1 := by rw [← e2, ← e4]; exact hzw.2
    exact Prod.ext (by linarith) (by linarith)

theorem S1_card : (S 1).card = 4 := by
  first
  | decide
  | rfl

end TwoSq

#print axioms TwoSq.inert_le
#print axioms TwoSq.two_le
#print axioms TwoSq.S1_card
