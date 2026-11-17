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


/-! ### Stage66d: the bound |S u| <= 4 * Mq u  (UNTESTED, not compiled anywhere)

`Sq'` and `Mq'` have exactly the bodies of `Section62.Sq` and `Section62.Mq` in Stage65 (those live in a
different file, so they are restated here; Stage67 identifies them by `rfl`).
PROVES (if it compiles):
  * Mq'_step        : p prime, p does not divide a, 0 < a, 0 < n  =>
                      Mq' (p^n * a) = (if p % 4 = 1 then n + 1 else 1) * Mq' a
  * pow2_le         : |S (2^n * a)| <= |S a|
  * inert_pow_even  : p = 3 mod 4  =>  |S (p^(2k) * a)| <= |S a|
  * inert_empty     : p = 3 mod 4, p | u, p^2 does not divide u  =>  |S u| = 0
  * card_le_four_Mq : 0 < u  =>  |S u| <= 4 * Mq' u
DOES NOT PROVE: the link to Section42.R2 or to Mn (stage 66e), nor hr2 itself. -/

namespace TwoSq

def Sq' (u : ℕ) : Finset ℕ := u.primeFactors.filter (fun q => q % 4 = 1)

def Mq' (u : ℕ) : ℕ := ∏ q ∈ Sq' u, (u.factorization q + 1)

lemma Mq'_step {p a n : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (ha : 0 < a) (hn : 0 < n) :
    Mq' (p ^ n * a) = (if p % 4 = 1 then n + 1 else 1) * Mq' a := by
  have ha0 : a ≠ 0 := ha.ne'
  have hpn0 : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero
  have hpf : (p ^ n * a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hpn0 ha0, Nat.primeFactors_prime_pow hn.ne' hp]
    exact (Finset.insert_eq p a.primeFactors).symm
  have hnot : p ∉ a.primeFactors := fun h => hpa (Nat.dvd_of_mem_primeFactors h)
  have hfac_p : (p ^ n * a).factorization p = n := by
    rw [Nat.factorization_mul hpn0 ha0, Finsupp.add_apply, hp.factorization_pow,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpa]
    simp
  have hfac_q : ∀ q, q ≠ p → (p ^ n * a).factorization q = a.factorization q := by
    intro q hq
    rw [Nat.factorization_mul hpn0 ha0, Finsupp.add_apply, hp.factorization_pow,
      Finsupp.single_apply, if_neg (Ne.symm hq)]
    simp
  unfold Mq' Sq'
  by_cases h1 : p % 4 = 1
  · simp only [hpf, Finset.filter_insert, h1, if_true]
    rw [Finset.prod_insert, hfac_p]
    · congr 1
      refine Finset.prod_congr rfl (fun q hq => ?_)
      have hqp : q ≠ p := by
        rintro rfl
        exact hnot (Finset.mem_filter.1 hq).1
      rw [hfac_q q hqp]
    · exact fun h => hnot (Finset.mem_filter.1 h).1
  · simp only [hpf, Finset.filter_insert, h1, if_false, one_mul]
    refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqp : q ≠ p := by
      rintro rfl
      exact hnot (Finset.mem_filter.1 hq).1
    rw [hfac_q q hqp]

lemma pow2_le (a : ℕ) : ∀ n : ℕ, (S (2 ^ n * a)).card ≤ (S a).card := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 ^ (n + 1) * a = 2 * (2 ^ n * a) := by ring
    rw [e]
    have h := two_le (u := 2 * (2 ^ n * a)) (dvd_mul_right 2 _)
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h
    exact h.trans ih

lemma inert_pow_even {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (a : ℕ) :
    ∀ k : ℕ, (S (p ^ (2 * k) * a)).card ≤ (S a).card := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : p ^ (2 * (k + 1)) * a = p ^ 2 * (p ^ (2 * k) * a) := by ring
    rw [e]
    have hpu : p ∣ p ^ 2 * (p ^ (2 * k) * a) :=
      Dvd.dvd.mul_right (dvd_pow_self p (by norm_num)) _
    have h := inert_le hp h3 hpu
    have hdiv : p ^ 2 * (p ^ (2 * k) * a) / p ^ 2 = p ^ (2 * k) * a :=
      Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)
    rw [hdiv] at h
    exact h.trans ih

lemma inert_empty {p u : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpu : p ∣ u) (hsq : ¬ p ^ 2 ∣ u) :
    (S u).card = 0 := by
  rcases (S u).eq_empty_or_nonempty with h | ⟨z, hz⟩
  · rw [h]; simp
  · exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inert_dvd hp h3 hpu hz
    have hs := (mem_S u z).1 hz
    rw [ha, hb] at hs
    have hd : ((p ^ 2 : ℕ) : ℤ) ∣ (u : ℤ) := ⟨a ^ 2 + b ^ 2, by push_cast; linarith⟩
    exact hsq (Int.natCast_dvd_natCast.1 hd)

theorem card_le_four_Mq : ∀ u : ℕ, 0 < u → (S u).card ≤ 4 * Mq' u := by
  intro u
  refine Nat.recOnPrimePow ?_ ?_ ?_ u
  · intro h
    exact absurd h (lt_irrefl 0)
  · intro _
    have h1 : Mq' 1 = 1 := by simp [Mq', Sq']
    rw [h1, S1_card]
  · intro a p n hp hpa hn ih hu
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hu)
    have iha := ih ha
    rw [Mq'_step hp hpa ha hn]
    rcases hp.eq_two_or_odd with rfl | hodd
    · have hne : (2 : ℕ) % 4 ≠ 1 := by norm_num
      rw [if_neg hne, one_mul]
      exact (pow2_le a n).trans iha
    · by_cases h1 : p % 4 = 1
      · haveI : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
        have hxyZ : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hxy
        rw [closed_form hp h1 hxyZ a hpa n, if_pos h1]
        calc (n + 1) * (S a).card ≤ (n + 1) * (4 * Mq' a) := Nat.mul_le_mul_left _ iha
          _ = 4 * ((n + 1) * Mq' a) := by ring
      · have h3 : p % 4 = 3 := by omega
        rw [if_neg h1, one_mul]
        obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
        · subst hk
          exact (inert_pow_even hp h3 a k).trans iha
        · subst hk
          have hle : (S (p ^ (2 * k + 1) * a)).card ≤ (S (p * a)).card := by
            have e : p ^ (2 * k + 1) * a = p ^ (2 * k) * (p * a) := by ring
            rw [e]
            exact inert_pow_even hp h3 (p * a) k
          have hz : (S (p * a)).card = 0 := by
            refine inert_empty hp h3 (dvd_mul_right p a) (fun hd => hpa ?_)
            rw [pow_two] at hd
            exact Nat.dvd_of_mul_dvd_mul_left hp.pos hd
          omega

end TwoSq

#print axioms TwoSq.Mq'_step
#print axioms TwoSq.card_le_four_Mq


/-! Stage66e (fast file only): the definitions below are copied verbatim from Stage65
(Section42.R2, Section62.Sq / Mq / Mn) so this file is standalone; Stage67 uses the real ones. -/

namespace Section42
noncomputable def R2 (n : ℕ) (u : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun q => q.1 ^ 2 + q.2 ^ 2 = u)
end Section42

namespace Section62
def Sq (u : ℕ) : Finset ℕ := u.primeFactors.filter (fun q => q % 4 = 1)
def Mq (u : ℕ) : ℕ := ∏ q ∈ Sq u, (u.factorization q + 1)
def Mn (n : ℕ) : ℕ := (Finset.Icc 1 n).sup Mq
end Section62


/-! ### Stage66e: from the two-square count to `Hr2`  (UNTESTED, not compiled anywhere)

PROVES (if it compiles):
  * R2_eq_S : v <= n  =>  Section42.R2 n (v : Z) = TwoSq.S v   (the box [-n,n]^2 contains every point of norm v <= n)
  * hr2_all : 1 <= u <= n  =>  card (Section42.R2 n u) <= 4 * Section62.Mn n
Uses: TwoSq.card_le_four_Mq (Stage66d), and `TwoSq.Mq' v = Section62.Mq v` by `rfl` (same bodies).
DOES NOT PROVE: H31 or HJac. -/

namespace Section66e

lemma R2_eq_S {n v : ℕ} (hv : v ≤ n) : Section42.R2 n (v : ℤ) = TwoSq.S v := by
  ext q
  rw [TwoSq.mem_S]
  unfold Section42.R2
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    have hn : (v : ℤ) ≤ (n : ℤ) := by exact_mod_cast hv
    have ha : q.1 ≤ q.1 ^ 2 := TwoSq.le_sq' q.1
    have ha' : -q.1 ≤ q.1 ^ 2 := by
      have := TwoSq.le_sq' (-q.1)
      rwa [neg_sq] at this
    have hb : q.2 ≤ q.2 ^ 2 := TwoSq.le_sq' q.2
    have hb' : -q.2 ≤ q.2 ^ 2 := by
      have := TwoSq.le_sq' (-q.2)
      rwa [neg_sq] at this
    have h1 : q.1 ^ 2 ≤ (v : ℤ) := by nlinarith [sq_nonneg q.2, h]
    have h2 : q.2 ^ 2 ≤ (v : ℤ) := by nlinarith [sq_nonneg q.1, h]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;> linarith

theorem hr2_all (n : ℕ) (u : ℤ) (hu : 1 ≤ u) (hun : u ≤ (n : ℤ)) :
    (Section42.R2 n u).card ≤ 4 * Section62.Mn n := by
  obtain ⟨v, rfl⟩ : ∃ v : ℕ, u = (v : ℤ) :=
    ⟨u.toNat, (Int.toNat_of_nonneg (by linarith)).symm⟩
  have hv1 : 1 ≤ v := by exact_mod_cast hu
  have hvn : v ≤ n := by exact_mod_cast hun
  rw [R2_eq_S hvn]
  refine (TwoSq.card_le_four_Mq v (by omega)).trans ?_
  have hmem : v ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hv1, hvn⟩
  have hle : Section62.Mq v ≤ Section62.Mn n := Finset.le_sup (f := Section62.Mq) hmem
  have hbr : TwoSq.Mq' v = Section62.Mq v := rfl
  rw [hbr]
  exact Nat.mul_le_mul_left 4 hle

end Section66e

#print axioms Section66e.R2_eq_S
#print axioms Section66e.hr2_all
