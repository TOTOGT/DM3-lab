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
  decide

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


/-! ### Stage66c: the overlap and the closed form (UNTESTED, not compiled anywhere)

Setting as in Stage66b: q prime with q = 1 mod 4 and x^2 + y^2 = q.
PROVES (if it compiles):
  * split_nodvd : q does not divide t  =>  |S (q t)| = 2 |S t|
  * split_dvd   : |S (q (q s))| + |S s| = 2 |S (q s)|
  * closed_form : q does not divide v  =>  |S (q^e v)| = (e+1) |S v|
No floor division anywhere: the case q | t is written t = q s.
DOES NOT PROVE: anything about Mq, R2, Mn or hr2 (stage 66d, 66e). -/

namespace TwoSq

lemma sq_gt (q c : ℤ) (hq : 2 ≤ q) (hc : c ≠ 0) : q < (q * c) ^ 2 := by
  have h1 : 0 < c ^ 2 := by positivity
  have h2 : 1 ≤ c ^ 2 := by linarith
  have h3 : (q * c) ^ 2 = q ^ 2 * c ^ 2 := by ring
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg q), hq]

lemma not_dvd_x {q : ℕ} (hq : q.Prime) {x y : ℤ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) :
    ¬ (q : ℤ) ∣ x := by
  rintro ⟨c, hc⟩
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  by_cases hc0 : c = 0
  · subst hc0
    have hx0 : x = 0 := by rw [hc]; ring
    have hy : y ^ 2 = (q : ℤ) := by rw [hx0] at hxy; linarith
    have hdv : (q : ℤ) ∣ y ^ 2 := ⟨1, by linarith⟩
    obtain ⟨d, hd⟩ := hqp.dvd_of_dvd_pow hdv
    by_cases hd0 : d = 0
    · have hy0 : y = 0 := by rw [hd, hd0]; ring
      rw [hy0] at hy
      nlinarith
    · have hlt := sq_gt q d hq2 hd0
      rw [← hd] at hlt
      linarith
  · have hlt := sq_gt q c hq2 hc0
    rw [← hc] at hlt
    nlinarith [sq_nonneg y]

lemma not_dvd_y {q : ℕ} (hq : q.Prime) {x y : ℤ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) :
    ¬ (q : ℤ) ∣ y :=
  not_dvd_x hq (x := y) (y := x) (by linarith)

lemma not_dvd_two {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) : ¬ (q : ℤ) ∣ 2 := by
  intro h
  have h' : q ∣ 2 := by exact_mod_cast h
  have h2 := Nat.le_of_dvd (by norm_num) h'
  have h3 := hq.two_le
  omega

lemma inter_dvd {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) {x y : ℤ}
    (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) {t : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ (S t).image (mP x y) ∩ (S t).image (mQ x y)) :
    (q : ℤ) ∣ z.1 ∧ (q : ℤ) ∣ z.2 := by
  obtain ⟨hA, hB⟩ := Finset.mem_inter.1 hz
  obtain ⟨w, -, hw⟩ := Finset.mem_image.1 hA
  obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hB
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  subst hw
  simp only [mP, mQ, Prod.mk.injEq] at hw'
  obtain ⟨e1, e2⟩ := hw'
  have h1 : 2 * (w.1 * x - w.2 * y) * x = (q : ℤ) * (w.1 + w'.1) := by
    linear_combination (-x) * e1 + y * e2 + (w.1 + w'.1) * hxy
  have h2 : 2 * (w.1 * y + w.2 * x) * y = (q : ℤ) * (w.1 - w'.1) := by
    linear_combination x * e1 - y * e2 + (w.1 - w'.1) * hxy
  have d1 : (q : ℤ) ∣ (2 * x) * (w.1 * x - w.2 * y) :=
    ⟨w.1 + w'.1, by linear_combination h1⟩
  have d2 : (q : ℤ) ∣ (2 * y) * (w.1 * y + w.2 * x) :=
    ⟨w.1 - w'.1, by linear_combination h2⟩
  simp only [mP]
  constructor
  · rcases hqp.dvd_or_dvd d1 with h | h
    · exfalso
      rcases hqp.dvd_or_dvd h with h' | h'
      · exact not_dvd_two hq hq1 h'
      · exact not_dvd_x hq hxy h'
    · exact h
  · rcases hqp.dvd_or_dvd d2 with h | h
    · exfalso
      rcases hqp.dvd_or_dvd h with h' | h'
      · exact not_dvd_two hq hq1 h'
      · exact not_dvd_y hq hxy h'
    · exact h

lemma inter_mem_S {q : ℕ} {x y : ℤ} (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) {t : ℕ} {z : ℤ × ℤ}
    (hz : z ∈ (S t).image (mP x y) ∩ (S t).image (mQ x y)) : z ∈ S (q * t) := by
  obtain ⟨hA, -⟩ := Finset.mem_inter.1 hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hA
  exact mem_mP hxy hw

lemma smul_inj {q : ℕ} (hq : q.Prime) :
    Function.Injective (fun w : ℤ × ℤ => ((q : ℤ) * w.1, (q : ℤ) * w.2)) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (mul_left_cancel₀ hq0 h.1) (mul_left_cancel₀ hq0 h.2)

lemma inter_eq_empty {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) {x y : ℤ}
    (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) (t : ℕ) (hqt : ¬ q ∣ t) :
    (S t).image (mP x y) ∩ (S t).image (mQ x y) = ∅ := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rcases ((S t).image (mP x y) ∩ (S t).image (mQ x y)).eq_empty_or_nonempty with h | ⟨z, hz⟩
  · exact h
  · exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inter_dvd hq hq1 hxy hz
    have hS := (mem_S _ z).1 (inter_mem_S hxy hz)
    rw [ha, hb] at hS
    push_cast at hS
    have hm : (q : ℤ) * ((q : ℤ) * (a ^ 2 + b ^ 2)) = (q : ℤ) * t := by linarith
    have ht : (a ^ 2 + b ^ 2) * (q : ℤ) = t := by
      have := mul_left_cancel₀ hq0 hm
      linarith
    have hdv : (q : ℤ) ∣ (t : ℤ) := ⟨a ^ 2 + b ^ 2, by linarith⟩
    exact hqt (Int.natCast_dvd_natCast.1 hdv)

lemma inter_eq_of_dvd {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) {x y : ℤ}
    (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) (s : ℕ) :
    (S (q * s)).image (mP x y) ∩ (S (q * s)).image (mQ x y)
      = (S s).image (fun w : ℤ × ℤ => ((q : ℤ) * w.1, (q : ℤ) * w.2)) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  ext z
  constructor
  · intro hz
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inter_dvd hq hq1 hxy hz
    have hS := (mem_S _ z).1 (inter_mem_S hxy hz)
    rw [ha, hb] at hS
    push_cast at hS
    have hm : (q : ℤ) * ((q : ℤ) * (a ^ 2 + b ^ 2)) = (q : ℤ) * ((q : ℤ) * s) := by linarith
    have hab : a ^ 2 + b ^ 2 = (s : ℤ) :=
      mul_left_cancel₀ hq0 (mul_left_cancel₀ hq0 hm)
    refine Finset.mem_image.2 ⟨(a, b), (mem_S s _).2 hab, ?_⟩
    exact Prod.ext ha.symm hb.symm
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
    refine Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨mQ x y w, mem_mQ hxy hw, ?_⟩,
      Finset.mem_image.2 ⟨mP x y w, mem_mP hxy hw, ?_⟩⟩
    · apply Prod.ext
      · simp only [mP, mQ]; linear_combination w.1 * hxy
      · simp only [mP, mQ]; linear_combination w.2 * hxy
    · apply Prod.ext
      · simp only [mP, mQ]; linear_combination w.1 * hxy
      · simp only [mP, mQ]; linear_combination w.2 * hxy

theorem split_nodvd {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) {x y : ℤ}
    (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) (t : ℕ) (hqt : ¬ q ∣ t) :
    (S (q * t)).card = 2 * (S t).card := by
  have h := split_sum hq hxy t
  rw [inter_eq_empty hq hq1 hxy t hqt] at h
  simpa using h

theorem split_dvd {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) {x y : ℤ}
    (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) (s : ℕ) :
    (S (q * (q * s))).card + (S s).card = 2 * (S (q * s)).card := by
  have h := split_sum hq hxy (q * s)
  rw [inter_eq_of_dvd hq hq1 hxy s, Finset.card_image_of_injective _ (smul_inj hq)] at h
  exact h

theorem closed_form {q : ℕ} (hq : q.Prime) (hq1 : q % 4 = 1) {x y : ℤ}
    (hxy : x ^ 2 + y ^ 2 = (q : ℤ)) (v : ℕ) (hv : ¬ q ∣ v) (e : ℕ) :
    (S (q ^ e * v)).card = (e + 1) * (S v).card := by
  have key : ∀ e : ℕ, (S (q ^ e * v)).card = (e + 1) * (S v).card ∧
      (S (q ^ (e + 1) * v)).card = (e + 2) * (S v).card := by
    intro e
    induction e with
    | zero =>
      refine ⟨by simp, ?_⟩
      have h := split_nodvd hq hq1 hxy v hv
      simpa using h
    | succ e ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨by rw [h1], ?_⟩
      have hs := split_dvd hq hq1 hxy (q ^ e * v)
      have e1 : q ^ (e + 1 + 1) * v = q * (q * (q ^ e * v)) := by ring
      have e2 : q ^ (e + 1) * v = q * (q ^ e * v) := by ring
      rw [e2] at h1
      rw [h0, h1] at hs
      rw [e1]
      nlinarith [hs]
  exact (key e).1

end TwoSq

#print axioms TwoSq.inert_le
#print axioms TwoSq.two_le
#print axioms TwoSq.S1_card
#print axioms TwoSq.split_sum
#print axioms TwoSq.split_nodvd
#print axioms TwoSq.split_dvd
#print axioms TwoSq.closed_form
