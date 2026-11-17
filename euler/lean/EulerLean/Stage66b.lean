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


/-! ### Stage66b: the splitting step for q = 1 mod 4 (UNTESTED, not compiled anywhere)

Fix a prime q and integers x, y with x^2 + y^2 = q (so q = 1 mod 4 or q = 2; the lemmas below only use
that q is prime and x^2+y^2 = q).  Write pi = x + y i, and for w = (w1, w2) let
  mP w = w * pi,   mQ w = w * conj(pi).
PROVES (if it compiles): |S (q t)| + |A inter B| = 2 |S t|  with  A = mP(S t),  B = mQ(S t).
DOES NOT PROVE: any count of A inter B (stage 66c), anything about Mq, R2, Mn, hr2. -/

namespace TwoSq

def mP (x y : ℤ) (w : ℤ × ℤ) : ℤ × ℤ := (w.1 * x - w.2 * y, w.1 * y + w.2 * x)
def mQ (x y : ℤ) (w : ℤ × ℤ) : ℤ × ℤ := (w.1 * x + w.2 * y, w.2 * x - w.1 * y)

lemma normP (x y : ℤ) (w : ℤ × ℤ) :
    (mP x y w).1 ^ 2 + (mP x y w).2 ^ 2 = (x ^ 2 + y ^ 2) * (w.1 ^ 2 + w.2 ^ 2) := by
  simp only [mP]; ring

lemma normQ (x y : ℤ) (w : ℤ × ℤ) :
    (mQ x y w).1 ^ 2 + (mQ x y w).2 ^ 2 = (x ^ 2 + y ^ 2) * (w.1 ^ 2 + w.2 ^ 2) := by
  simp only [mQ]; ring

lemma injP {x y : ℤ} (h : 0 < x ^ 2 + y ^ 2) : Function.Injective (mP x y) := by
  intro w w' hw
  simp only [mP, Prod.mk.injEq] at hw
  obtain ⟨e1, e2⟩ := hw
  have h1 : (x ^ 2 + y ^ 2) * (w.1 - w'.1) = 0 := by linear_combination x * e1 + y * e2
  have h2 : (x ^ 2 + y ^ 2) * (w.2 - w'.2) = 0 := by linear_combination (-y) * e1 + x * e2
  have a1 := (mul_eq_zero.1 h1).resolve_left h.ne'
  have a2 := (mul_eq_zero.1 h2).resolve_left h.ne'
  exact Prod.ext (by linarith) (by linarith)

lemma injQ {x y : ℤ} (h : 0 < x ^ 2 + y ^ 2) : Function.Injective (mQ x y) := by
  intro w w' hw
  simp only [mQ, Prod.mk.injEq] at hw
  obtain ⟨e1, e2⟩ := hw
  have h1 : (x ^ 2 + y ^ 2) * (w.1 - w'.1) = 0 := by linear_combination x * e1 - y * e2
  have h2 : (x ^ 2 + y ^ 2) * (w.2 - w'.2) = 0 := by linear_combination y * e1 + x * e2
  have a1 := (mul_eq_zero.1 h1).resolve_left h.ne'
  have a2 := (mul_eq_zero.1 h2).resolve_left h.ne'
  exact Prod.ext (by linarith) (by linarith)

lemma mem_mP {x y : ℤ} {q t : ℕ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) {w : ℤ × ℤ} (hw : w ∈ S t) :
    mP x y w ∈ S (q * t) := by
  rw [mem_S] at hw ⊢
  rw [normP, hxy, hw]
  norm_cast

lemma mem_mQ {x y : ℤ} {q t : ℕ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) {w : ℤ × ℤ} (hw : w ∈ S t) :
    mQ x y w ∈ S (q * t) := by
  rw [mem_S] at hw ⊢
  rw [normQ, hxy, hw]
  norm_cast

lemma cover {q : ℕ} (hq : q.Prime) {x y : ℤ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) {t : ℕ}
    {z : ℤ × ℤ} (hz : z ∈ S (q * t)) :
    (∃ w ∈ S t, mP x y w = z) ∨ (∃ w ∈ S t, mQ x y w = z) := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hN : z.1 ^ 2 + z.2 ^ 2 = (q : ℤ) * t := by
    have := (mem_S _ z).1 hz
    push_cast at this
    exact this
  have hprod : (q : ℤ) ∣ (z.1 * x + z.2 * y) * (z.1 * x - z.2 * y) :=
    ⟨z.1 ^ 2 - y ^ 2 * t, by linear_combination z.1 ^ 2 * hxy - y ^ 2 * hN⟩
  rcases hqp.dvd_or_dvd hprod with h | h
  · obtain ⟨a, ha⟩ := h
    have hQ2 : (z.2 * x - z.1 * y) ^ 2 = (q : ℤ) * ((q : ℤ) * (t - a ^ 2)) := by
      linear_combination (z.1 ^ 2 + z.2 ^ 2) * hxy + (q : ℤ) * hN
        - (z.1 * x + z.2 * y + q * a) * ha
    have hQ : (q : ℤ) ∣ z.2 * x - z.1 * y := hqp.dvd_of_dvd_pow ⟨(q : ℤ) * (t - a ^ 2), hQ2⟩
    obtain ⟨b, hb⟩ := hQ
    have hab : a ^ 2 + b ^ 2 = (t : ℤ) := by
      have e1 : (q : ℤ) ^ 2 * (a ^ 2 + b ^ 2)
          = (z.1 * x + z.2 * y) ^ 2 + (z.2 * x - z.1 * y) ^ 2 := by rw [ha, hb]; ring
      have e2 : (z.1 * x + z.2 * y) ^ 2 + (z.2 * x - z.1 * y) ^ 2
          = (x ^ 2 + y ^ 2) * (z.1 ^ 2 + z.2 ^ 2) := by ring
      have e : (q : ℤ) ^ 2 * (a ^ 2 + b ^ 2) = (q : ℤ) ^ 2 * t := by
        rw [e1, e2, hxy, hN]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hq0) e
    left
    refine ⟨(a, b), (mem_S t _).2 hab, ?_⟩
    apply Prod.ext
    · apply mul_left_cancel₀ hq0
      show (q : ℤ) * (a * x - b * y) = (q : ℤ) * z.1
      linear_combination z.1 * hxy - x * ha + y * hb
    · apply mul_left_cancel₀ hq0
      show (q : ℤ) * (a * y + b * x) = (q : ℤ) * z.2
      linear_combination z.2 * hxy - y * ha - x * hb
  · obtain ⟨a, ha⟩ := h
    have hQ2 : (z.2 * x + z.1 * y) ^ 2 = (q : ℤ) * ((q : ℤ) * (t - a ^ 2)) := by
      linear_combination (z.1 ^ 2 + z.2 ^ 2) * hxy + (q : ℤ) * hN
        - (z.1 * x - z.2 * y + q * a) * ha
    have hQ : (q : ℤ) ∣ z.2 * x + z.1 * y := hqp.dvd_of_dvd_pow ⟨(q : ℤ) * (t - a ^ 2), hQ2⟩
    obtain ⟨b, hb⟩ := hQ
    have hab : a ^ 2 + b ^ 2 = (t : ℤ) := by
      have e1 : (q : ℤ) ^ 2 * (a ^ 2 + b ^ 2)
          = (z.1 * x - z.2 * y) ^ 2 + (z.2 * x + z.1 * y) ^ 2 := by rw [ha, hb]; ring
      have e2 : (z.1 * x - z.2 * y) ^ 2 + (z.2 * x + z.1 * y) ^ 2
          = (x ^ 2 + y ^ 2) * (z.1 ^ 2 + z.2 ^ 2) := by ring
      have e : (q : ℤ) ^ 2 * (a ^ 2 + b ^ 2) = (q : ℤ) ^ 2 * t := by
        rw [e1, e2, hxy, hN]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hq0) e
    right
    refine ⟨(a, b), (mem_S t _).2 hab, ?_⟩
    apply Prod.ext
    · apply mul_left_cancel₀ hq0
      show (q : ℤ) * (a * x + b * y) = (q : ℤ) * z.1
      linear_combination z.1 * hxy - x * ha - y * hb
    · apply mul_left_cancel₀ hq0
      show (q : ℤ) * (b * x - a * y) = (q : ℤ) * z.2
      linear_combination z.2 * hxy + y * ha - x * hb

theorem split_sum {q : ℕ} (hq : q.Prime) {x y : ℤ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) (t : ℕ) :
    (S (q * t)).card + (((S t).image (mP x y)) ∩ ((S t).image (mQ x y))).card
      = 2 * (S t).card := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by rw [hxy]; exact_mod_cast hq.pos
  have hU : S (q * t) = (S t).image (mP x y) ∪ (S t).image (mQ x y) := by
    ext z
    constructor
    · intro hz
      rcases cover hq hxy hz with ⟨w, hw, e⟩ | ⟨w, hw, e⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨w, hw, e⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hw, e⟩)
    · intro hz
      rcases Finset.mem_union.1 hz with h | h
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
        exact mem_mP hxy hw
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
        exact mem_mQ hxy hw
  rw [hU, Finset.card_union_add_card_inter, Finset.card_image_of_injective _ (injP hpos),
    Finset.card_image_of_injective _ (injQ hpos)]
  ring

end TwoSq

#print axioms TwoSq.inert_le
#print axioms TwoSq.two_le
#print axioms TwoSq.S1_card
#print axioms TwoSq.split_sum
