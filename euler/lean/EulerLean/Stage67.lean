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

/-! ===== Stage65 follows ===== -/

/-! Stage64: Stage63b + Sufficiency23 + FourSquaresMixed merged (no cross-file imports in this project), then Section64.
    UNTESTED when written (Section64 only; the three merged parts are the files already run). -/

/-! Stage63b: merged file. Each earlier file appears once. UNTESTED when written. -/


/-!
# Lemma 5.1: the local-factor maximization (fifth-power form)
(Howe-Huffman-Kohlmeyer-Kruer, hexagon:2611.00370v1)

The paper bounds the local factor (e+1)/p^(e/5). Raising to the fifth power, the bare statement is

    (e+1)^5 * p^a ≤ (a+1)^5 * p^e      for every e ≥ 1,

where a is the "maximizing positive exponent" in the paper's table:
    p ≡ 3 mod 4, p < 32 :  p = 3, 7, 11, 19, 23, 31  with  a = 4, 2, 1, 1, 1, 1
    q ≡ 1 mod 4, q < 32 :  q = 5, 13, 17, 29         with  a = 2, 1, 1, 1
and, for primes p ≥ 32 and every e,   (e+1)^5 ≤ p^e   (so the local factor is ≤ 1).

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this). The side
conditions were checked by exact integer arithmetic in Python first (all ten primes, e < 200).

WHAT THIS FILE DOES NOT DO (so it is not read as more than it is):
* It is only the bare factor (e+1)/p^(e/5). The first bound of Lemma 5.1 carries an extra
  factor p/(p+1); for p = 31 the bare factor exceeds 1 at e = 1 (32/31), and it is that extra
  factor that makes the C1 local bound <= 1 there. That is handled in Section6Arithmetic.lean's
  constants, not here.
* It does not multiply the local bounds over the prime factorization of m, and it does not
  pass from fifth powers to real fifth roots. Those steps are separate and not done.
-/

namespace LocalFactors

/-- the step inequality persists for larger exponents:
    if (a+2)^5 ≤ p (a+1)^5 then (e+2)^5 ≤ p (e+1)^5 for all e ≥ a. -/
lemma step_persists (p a e : ℕ) (hstep : (a + 2) ^ 5 ≤ p * (a + 1) ^ 5) (hae : a ≤ e) :
    (e + 2) ^ 5 ≤ p * (e + 1) ^ 5 := by
  have hu : 0 < (a + 1) ^ 5 := by positivity
  have h1 : (e + 2) * (a + 1) ≤ (a + 2) * (e + 1) := by nlinarith
  have h2 : ((e + 2) * (a + 1)) ^ 5 ≤ ((a + 2) * (e + 1)) ^ 5 := Nat.pow_le_pow_left h1 5
  rw [mul_pow, mul_pow] at h2
  have h3 : (e + 2) ^ 5 * (a + 1) ^ 5 ≤ p * (e + 1) ^ 5 * (a + 1) ^ 5 := by
    calc (e + 2) ^ 5 * (a + 1) ^ 5 ≤ (a + 2) ^ 5 * (e + 1) ^ 5 := h2
      _ ≤ (p * (a + 1) ^ 5) * (e + 1) ^ 5 := Nat.mul_le_mul_right _ hstep
      _ = p * (e + 1) ^ 5 * (a + 1) ^ 5 := by ring
  exact Nat.le_of_mul_le_mul_right h3 hu

/-- beyond the maximizing exponent a, the quantity (e+1)^5 / p^e keeps decreasing -/
lemma beyond (p a : ℕ) (hstep : (a + 2) ^ 5 ≤ p * (a + 1) ^ 5) :
    ∀ e, a ≤ e → (e + 1) ^ 5 * p ^ a ≤ (a + 1) ^ 5 * p ^ e := by
  intro e hae
  induction e, hae using Nat.le_induction with
  | base => exact le_refl _
  | succ e hae ih =>
    have hs := step_persists p a e hstep hae
    calc (e + 1 + 1) ^ 5 * p ^ a = (e + 2) ^ 5 * p ^ a := by ring
      _ ≤ (p * (e + 1) ^ 5) * p ^ a := Nat.mul_le_mul_right _ hs
      _ = p * ((e + 1) ^ 5 * p ^ a) := by ring
      _ ≤ p * ((a + 1) ^ 5 * p ^ e) := Nat.mul_le_mul_left _ ih
      _ = (a + 1) ^ 5 * p ^ (e + 1) := by ring

/-- the general maximization statement: a finite check below a, `beyond` above. -/
theorem local_max (p a : ℕ) (hstep : (a + 2) ^ 5 ≤ p * (a + 1) ^ 5)
    (hsmall : ∀ e < a, (e + 1) ^ 5 * p ^ a ≤ (a + 1) ^ 5 * p ^ e) :
    ∀ e, (e + 1) ^ 5 * p ^ a ≤ (a + 1) ^ 5 * p ^ e := by
  intro e
  by_cases h : e < a
  · exact hsmall e h
  · exact beyond p a hstep e (not_lt.1 h)

/-- primes p ≥ 32: the local factor is at most 1, i.e. (e+1)^5 ≤ p^e for every e. -/
theorem large_prime (p e : ℕ) (hp : 32 ≤ p) : (e + 1) ^ 5 ≤ p ^ e := by
  have h1 : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
  calc (e + 1) ^ 5 ≤ (2 ^ e) ^ 5 := Nat.pow_le_pow_left h1 5
    _ = 32 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ p ^ e := Nat.pow_le_pow_left hp e

/-! ### The ten small primes of the paper's table -/

theorem max_p3  : ∀ e, (e + 1) ^ 5 * 3 ^ 4  ≤ 5 ^ 5 * 3 ^ e  :=
  local_max 3 4 (by norm_num) (by decide)
theorem max_p7  : ∀ e, (e + 1) ^ 5 * 7 ^ 2  ≤ 3 ^ 5 * 7 ^ e  :=
  local_max 7 2 (by norm_num) (by decide)
theorem max_p11 : ∀ e, (e + 1) ^ 5 * 11 ^ 1 ≤ 2 ^ 5 * 11 ^ e :=
  local_max 11 1 (by norm_num) (by decide)
theorem max_p19 : ∀ e, (e + 1) ^ 5 * 19 ^ 1 ≤ 2 ^ 5 * 19 ^ e :=
  local_max 19 1 (by norm_num) (by decide)
theorem max_p23 : ∀ e, (e + 1) ^ 5 * 23 ^ 1 ≤ 2 ^ 5 * 23 ^ e :=
  local_max 23 1 (by norm_num) (by decide)
theorem max_p31 : ∀ e, (e + 1) ^ 5 * 31 ^ 1 ≤ 2 ^ 5 * 31 ^ e :=
  local_max 31 1 (by norm_num) (by decide)
theorem max_q5  : ∀ e, (e + 1) ^ 5 * 5 ^ 2  ≤ 3 ^ 5 * 5 ^ e  :=
  local_max 5 2 (by norm_num) (by decide)
theorem max_q13 : ∀ e, (e + 1) ^ 5 * 13 ^ 1 ≤ 2 ^ 5 * 13 ^ e :=
  local_max 13 1 (by norm_num) (by decide)
theorem max_q17 : ∀ e, (e + 1) ^ 5 * 17 ^ 1 ≤ 2 ^ 5 * 17 ^ e :=
  local_max 17 1 (by norm_num) (by decide)
theorem max_q29 : ∀ e, (e + 1) ^ 5 * 29 ^ 1 ≤ 2 ^ 5 * 29 ^ e :=
  local_max 29 1 (by norm_num) (by decide)

end LocalFactors


/-!
# Lemma 5.1, first bound: tau(m) m / sigma(m) <= (23/10) m^(1/5)
(Howe-Huffman-Kohlmeyer-Kruer, hexagon:2611.00370v1), for m >= 1 all of whose prime factors are
= 3 mod 4 (this is the situation of Lemma 2.1: m odd, every prime divisor in P3).

STATUS: UNTESTED in Lean when written. The part above this comment is LocalFactors.lean
(compiled green in GitHub elementary runs #5 and #9).

WHAT THIS ADDS (once it compiles): the multiplicative assembly. With
    F(m) = tau(m)^5 m^4 / sigma(m)^5          (so (tau m * m / sigma m)^5 = F(m) * m),
F is multiplicative, F(p^e) <= (p/(p+1))^5 (e+1)^5 / p^e <= beta(p) for p in {3,7,11,19,23}
(beta = the fifth powers of the paper's local bounds) and <= 1 for every other prime = 3 mod 4,
so F(m) <= prod beta = 183143120027364343/2849934139195392 = C1^5 < (23/10)^5.
Then the fifth root.

NOT DONE HERE: the SECOND bound of Lemma 5.1, M(n) <= (11/5) n^(1/5). M(n) is not defined
anywhere in this project's Lean files, so that part is not formalized.
-/

namespace Section51

def tau (m : ℕ) : ℕ := ArithmeticFunction.sigma 0 m
def sig (m : ℕ) : ℕ := ArithmeticFunction.sigma 1 m

lemma tau_mul {a b : ℕ} (h : Nat.Coprime a b) : tau (a * b) = tau a * tau b :=
  (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_mul_of_coprime h

lemma sig_mul {a b : ℕ} (h : Nat.Coprime a b) : sig (a * b) = sig a * sig b :=
  (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

lemma tau_one : tau 1 = 1 := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_one
lemma sig_one : sig 1 = 1 := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_one

lemma tau_pp {p : ℕ} (hp : p.Prime) (e : ℕ) : tau (p ^ e) = e + 1 := by
  unfold tau
  exact ArithmeticFunction.sigma_zero_apply_prime_pow hp

lemma sig_pp {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sig (p ^ e) = ∑ k ∈ Finset.range (e + 1), p ^ k := by
  unfold sig
  exact ArithmeticFunction.sigma_one_apply_prime_pow hp

lemma sig_ge {m : ℕ} (hm : 0 < m) : m ≤ sig m := by
  unfold sig
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (f := fun d : ℕ => d) (fun d _ => Nat.zero_le d)
    (Nat.mem_divisors_self m hm.ne')

/-- F(m) = tau(m)^5 m^4 / sigma(m)^5, in the rationals -/
def Fq (m : ℕ) : ℚ := ((tau m : ℚ)) ^ 5 * (m : ℚ) ^ 4 / ((sig m : ℚ)) ^ 5

lemma Fq_nonneg (m : ℕ) : 0 ≤ Fq m := by unfold Fq; positivity

lemma Fq_mul {a b : ℕ} (h : Nat.Coprime a b) : Fq (a * b) = Fq a * Fq b := by
  unfold Fq
  rw [tau_mul h, sig_mul h]
  push_cast
  ring

lemma Fq_pp_eq {p : ℕ} (hp : p.Prime) (e : ℕ) :
    Fq (p ^ e) = ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 / ((sig (p ^ e) : ℕ) : ℚ) ^ 5 := by
  unfold Fq
  rw [tau_pp hp e]
  push_cast
  ring

/-! ### sigma(p^e) >= p^e (p+1)/p -/

lemma geom_ge (p : ℕ) : ∀ e, 1 ≤ e → p ^ e * (p + 1) ≤ p * ∑ k ∈ Finset.range (e + 1), p ^ k := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    have h2 : ∑ k ∈ Finset.range 2, p ^ k = 1 + p := by simp [Finset.sum_range_succ]
    rw [h2]
    apply le_of_eq
    ring
  | succ e he ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h1 : p ^ (e + 1) ≤ p ^ e * (p + 1) := by
      rw [pow_succ]
      nlinarith [Nat.zero_le (p ^ e)]
    have h2 : p ^ (e + 1) * (p + 1) = p ^ (e + 2) + p ^ (e + 1) := by ring
    have h3 : p * p ^ (e + 1) = p ^ (e + 2) := by ring
    linarith

lemma sigma_pp_ge {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e) :
    p ^ e * (p + 1) ≤ p * sig (p ^ e) := by
  rw [sig_pp hp e]
  exact geom_ge p e he

/-! ### the local bound in the rationals -/

lemma local_F (p e a s : ℕ) (hp : 0 < p) (hσ : p ^ e * (p + 1) ≤ p * s)
    (hmax : (e + 1) ^ 5 * p ^ a ≤ (a + 1) ^ 5 * p ^ e) :
    ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 / (s : ℚ) ^ 5
      ≤ (p : ℚ) ^ 5 * ((a : ℚ) + 1) ^ 5 / (((p : ℚ) + 1) ^ 5 * (p : ℚ) ^ a) := by
  have hσ' : (p : ℚ) ^ e * ((p : ℚ) + 1) ≤ (p : ℚ) * s := by exact_mod_cast hσ
  have hmax' : ((e : ℚ) + 1) ^ 5 * (p : ℚ) ^ a ≤ ((a : ℚ) + 1) ^ 5 * (p : ℚ) ^ e := by
    exact_mod_cast hmax
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hx : (0 : ℚ) < (p : ℚ) ^ e := by positivity
  have hs : (0 : ℚ) < s := by
    by_contra h
    have h' : (s : ℚ) ≤ 0 := not_lt.1 h
    nlinarith [mul_pos hx (show (0 : ℚ) < (p : ℚ) + 1 by positivity), hp', h', hσ']
  rw [div_le_div_iff₀ (pow_pos hs 5) (by positivity)]
  calc ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 * (((p : ℚ) + 1) ^ 5 * (p : ℚ) ^ a)
      = ((p : ℚ) ^ e) ^ 4 * ((p : ℚ) + 1) ^ 5 * (((e : ℚ) + 1) ^ 5 * (p : ℚ) ^ a) := by ring
    _ ≤ ((p : ℚ) ^ e) ^ 4 * ((p : ℚ) + 1) ^ 5 * (((a : ℚ) + 1) ^ 5 * (p : ℚ) ^ e) :=
        mul_le_mul_of_nonneg_left hmax' (by positivity)
    _ = ((a : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e * ((p : ℚ) + 1)) ^ 5 := by ring
    _ ≤ ((a : ℚ) + 1) ^ 5 * ((p : ℚ) * s) ^ 5 := by gcongr
    _ = (p : ℚ) ^ 5 * ((a : ℚ) + 1) ^ 5 * (s : ℚ) ^ 5 := by ring

lemma Fq_pp_le_of {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e) (a : ℕ)
    (hmax : (e + 1) ^ 5 * p ^ a ≤ (a + 1) ^ 5 * p ^ e) :
    Fq (p ^ e) ≤ (p : ℚ) ^ 5 * ((a : ℚ) + 1) ^ 5 / (((p : ℚ) + 1) ^ 5 * (p : ℚ) ^ a) := by
  rw [Fq_pp_eq hp e]
  exact local_F p e a (sig (p ^ e)) hp.pos (sigma_pp_ge hp he) hmax

/-- the fifth powers of the paper's local bounds (1 at every other prime) -/
def beta (p : ℕ) : ℚ :=
  if p = 3 then 9375 / 1024
  else if p = 7 then 83349 / 32768
  else if p = 11 then 14641 / 7776
  else if p = 19 then 130321 / 100000
  else if p = 23 then 279841 / 248832
  else 1

def S5 : Finset ℕ := {3, 7, 11, 19, 23}

lemma beta_ge_one {q : ℕ} (hq : q ∈ S5) : 1 ≤ beta q := by
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num [beta]

lemma beta_nonneg (q : ℕ) : 0 ≤ beta q := by
  unfold beta
  split_ifs <;> norm_num

lemma S5_prime {q : ℕ} (hq : q ∈ S5) : q.Prime := by
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Fq at a prime power with p = 3 mod 4: <= beta p for the five primes, <= 1 otherwise -/
lemma Fq_pp_le {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) {e : ℕ} (he : 1 ≤ e) :
    Fq (p ^ e) ≤ if p ∈ S5 then beta p else 1 := by
  by_cases hpS : p ∈ S5
  · rw [if_pos hpS]
    simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hpS
    rcases hpS with rfl | rfl | rfl | rfl | rfl
    · refine le_trans (Fq_pp_le_of hp he 4 (LocalFactors.max_p3 e)) ?_
      norm_num [beta]
    · refine le_trans (Fq_pp_le_of hp he 2 (LocalFactors.max_p7 e)) ?_
      norm_num [beta]
    · refine le_trans (Fq_pp_le_of hp he 1 (LocalFactors.max_p11 e)) ?_
      norm_num [beta]
    · refine le_trans (Fq_pp_le_of hp he 1 (LocalFactors.max_p19 e)) ?_
      norm_num [beta]
    · refine le_trans (Fq_pp_le_of hp he 1 (LocalFactors.max_p23 e)) ?_
      norm_num [beta]
  · rw [if_neg hpS]
    by_cases h32 : p < 32
    · have h6 : p = 3 ∨ p = 7 ∨ p = 11 ∨ p = 19 ∨ p = 23 ∨ p = 31 := by
        interval_cases p <;> first | omega | (norm_num at hp)
      rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (by simp [S5]) hpS
      · exact absurd (by simp [S5]) hpS
      · exact absurd (by simp [S5]) hpS
      · exact absurd (by simp [S5]) hpS
      · exact absurd (by simp [S5]) hpS
      · refine le_trans (Fq_pp_le_of hp he 1 (LocalFactors.max_p31 e)) ?_
        norm_num
    · have hp32 : 32 ≤ p := not_lt.1 h32
      have hmax : (e + 1) ^ 5 * p ^ 0 ≤ (0 + 1) ^ 5 * p ^ e := by
        simpa using LocalFactors.large_prime p e hp32
      refine le_trans (Fq_pp_le_of hp he 0 hmax) ?_
      have hp' : (0 : ℚ) < p := by exact_mod_cast hp.pos
      have h1 : (p : ℚ) ^ 5 ≤ ((p : ℚ) + 1) ^ 5 := by
        gcongr
        linarith
      rw [div_le_one (by positivity)]
      simpa using h1

/-! ### the multiplicative bookkeeping -/

/-- the product over the five special primes of (beta q if q | m, else 1) -/
def Phi (m : ℕ) : ℚ := ∏ q ∈ S5, (if q ∣ m then beta q else 1)

lemma Phi_nonneg (m : ℕ) : 0 ≤ Phi m := by
  unfold Phi
  apply Finset.prod_nonneg
  intro q _
  split_ifs
  · exact beta_nonneg q
  · norm_num

lemma Phi_one : Phi 1 = 1 := by
  unfold Phi
  apply Finset.prod_eq_one
  intro q hq
  rw [if_neg]
  intro hd
  have h1 := Nat.le_of_dvd one_pos hd
  have h2 := (S5_prime hq).two_le
  omega

lemma Phi_mul {a b : ℕ} (h : Nat.Coprime a b) : Phi (a * b) = Phi a * Phi b := by
  unfold Phi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  have hq' : q.Prime := S5_prime hq
  have hnot : ¬ (q ∣ a ∧ q ∣ b) := by
    rintro ⟨h1, h2⟩
    have hc : Nat.Coprime q q :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h2 h)
    exact hq'.ne_one (Nat.Coprime.eq_one_of_dvd hc (dvd_refl q))
  by_cases h1 : q ∣ a
  · have h2 : ¬ q ∣ b := fun h2 => hnot ⟨h1, h2⟩
    rw [if_pos (Dvd.dvd.mul_right h1 b), if_pos h1, if_neg h2, mul_one]
  · by_cases h2 : q ∣ b
    · rw [if_pos (Dvd.dvd.mul_left h2 a), if_neg h1, if_pos h2, one_mul]
    · have h3 : ¬ q ∣ a * b := fun h3 => by
        rcases hq'.dvd_mul.1 h3 with h3 | h3
        · exact h1 h3
        · exact h2 h3
      rw [if_neg h3, if_neg h1, if_neg h2, mul_one]

lemma Phi_pp {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    Phi (p ^ n) = if p ∈ S5 then beta p else 1 := by
  unfold Phi
  have hcong : ∀ q ∈ S5, (if q ∣ p ^ n then beta q else 1) = if q = p then beta q else 1 := by
    intro q hq
    have hqp := S5_prime hq
    by_cases h : q = p
    · have hd : q ∣ p ^ n := by
        rw [h]
        exact dvd_pow_self p (by omega : n ≠ 0)
      rw [if_pos hd, if_pos h]
    · have hd : ¬ q ∣ p ^ n := fun hd =>
        h ((Nat.prime_dvd_prime_iff_eq hqp hp).1 (hqp.dvd_of_dvd_pow hd))
      rw [if_neg hd, if_neg h]
  rw [Finset.prod_congr rfl hcong]
  rw [Finset.prod_ite_eq']

theorem Fq_le_Phi (m : ℕ) :
    0 < m → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → Fq m ≤ Phi m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ hmod
    have h4 := hmod p hp (dvd_pow_self p (by omega : n ≠ 0))
    rw [Phi_pp hp hn]
    exact Fq_pp_le hp h4 hn
  | zero => intro h; omega
  | one =>
    intro _ _
    have : Fq 1 = 1 := by unfold Fq; rw [tau_one, sig_one]; norm_num
    rw [this, Phi_one]
  | coprime a b ha hb hab iha ihb =>
    intro hm hmod
    rw [Fq_mul hab, Phi_mul hab]
    exact mul_le_mul (iha (by omega) (fun p hp hd => hmod p hp (dvd_mul_of_dvd_left hd b)))
      (ihb (by omega) (fun p hp hd => hmod p hp (dvd_mul_of_dvd_right hd a)))
      (Fq_nonneg b) (Phi_nonneg a)

/-- the fifth-power form of the first bound: F(m) <= C1^5 -/
theorem tau_sigma_pow5 (m : ℕ) (hm : 0 < m) (hmod : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) :
    Fq m ≤ 183143120027364343 / 2849934139195392 := by
  refine le_trans (Fq_le_Phi m hm hmod) ?_
  unfold Phi
  calc ∏ q ∈ S5, (if q ∣ m then beta q else 1) ≤ ∏ q ∈ S5, beta q := by
        apply Finset.prod_le_prod
        · intro q _
          split_ifs
          · exact beta_nonneg q
          · norm_num
        · intro q hq
          split_ifs
          · exact le_refl _
          · exact beta_ge_one hq
    _ = 183143120027364343 / 2849934139195392 := by
        norm_num [S5, beta, Finset.prod_insert]

/-- Lemma 5.1, first bound, with the real fifth root:
    tau(m) m / sigma(m) <= (23/10) m^(1/5) -/
theorem lemma51_first (m : ℕ) (hm : 0 < m)
    (hmod : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) :
    ((tau m : ℝ) * (m : ℝ) / (sig m : ℝ)) ≤ (23 / 10) * (m : ℝ) ^ ((1 : ℝ) / 5) := by
  have hq := tau_sigma_pow5 m hm hmod
  have hq' : ((Fq m : ℚ) : ℝ) ≤ ((183143120027364343 / 2849934139195392 : ℚ) : ℝ) :=
    Rat.cast_le.2 hq
  have hR : ((tau m : ℝ)) ^ 5 * (m : ℝ) ^ 4 / ((sig m : ℝ)) ^ 5
      ≤ (183143120027364343 / 2849934139195392 : ℝ) := by
    unfold Fq at hq'
    push_cast at hq'
    exact hq'
  have hsig : (0 : ℝ) < (sig m : ℝ) := by
    have := sig_ge hm
    have : 0 < sig m := lt_of_lt_of_le hm this
    exact_mod_cast this
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hX : 0 ≤ (tau m : ℝ) * (m : ℝ) / (sig m : ℝ) := by positivity
  have hY : 0 ≤ (23 / 10 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 5) := by positivity
  have h5 : ((m : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = (m : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
    norm_num
  have hy5 : ((23 / 10 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = (23 / 10 : ℝ) ^ 5 * (m : ℝ) := by
    rw [mul_pow, h5]
  have hx5 : ((tau m : ℝ) * (m : ℝ) / (sig m : ℝ)) ^ 5
      = ((tau m : ℝ)) ^ 5 * (m : ℝ) ^ 4 / ((sig m : ℝ)) ^ 5 * (m : ℝ) := by
    field_simp
  have hle : ((tau m : ℝ) * (m : ℝ) / (sig m : ℝ)) ^ 5
      ≤ ((23 / 10 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 := by
    rw [hx5, hy5]
    calc ((tau m : ℝ)) ^ 5 * (m : ℝ) ^ 4 / ((sig m : ℝ)) ^ 5 * (m : ℝ)
        ≤ (183143120027364343 / 2849934139195392 : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hR hmR.le
      _ ≤ (23 / 10 : ℝ) ^ 5 * (m : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) hmR.le
  first
    | exact (pow_le_pow_iff_left₀ hX hY (by norm_num)).1 hle
    | exact (pow_le_pow_iff_left hX hY (by norm_num)).1 hle

end Section51



/-!
# Lemma 4.1 of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1)

  For every t ≥ 0:  N_mix(t) ≤ 2(t+1),
  where N_mix(t) = #{(x,y) ∈ ℤ² : x+y odd, x²+y² ≤ t}.

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this).
Expect compile errors; fix them against what the compiler says.

What is formalized: the paper's own argument, in two pieces.
  (a) `Nmix_eq`   : N_mix(t) = 4 * #A(t), where A(t) is the quadrant x>0, y≥0
                    (quarter-turn r(x,y) = (-y,x) permutes the four quadrants).
  (b) `quarter_card` : 2 * #A(t) ≤ t+1, via the paper's label
                    L = u²+u+v+1 with x+y = 2u+1, x−y = 2v+1,
                    which is injective on A(t) and lands in [1, (t+1)/2].
Combined: `Nmix_le`.

Scope notes (so the statement is not read as more than it is):
* t is a natural number here. For real t, N_mix(t) = N_mix(⌊t⌋), so the integer
  case is the whole content; that reduction is not formalized.
* The bound is only an upper bound. Numerically, max N_mix(t)/(2(t+1)) = 1.0 for
  integer t in [0,4000] (script audit_lemma4.py), so the constant 2 is attained.
-/

namespace Section4
open Classical

/-- parity + norm condition defining the "mixed" pairs -/
def P (t : ℕ) (p : ℤ × ℤ) : Prop := (p.1 + p.2) % 2 = 1 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ (t : ℤ)

noncomputable def inBox (t : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t

/-- the set counted by N_mix(t) (cut to a finite box, which loses nothing: see `mem_Nset`) -/
noncomputable def Nset (t : ℕ) : Finset (ℤ × ℤ) := (inBox t).filter (P t)

noncomputable def Nmix (t : ℕ) : ℕ := (Nset t).card

lemma bound_of_sq {x : ℤ} {t : ℕ} (h : x ^ 2 ≤ (t : ℤ)) : -(t : ℤ) ≤ x ∧ x ≤ (t : ℤ) := by
  have ht : (0 : ℤ) ≤ t := Nat.cast_nonneg t
  constructor
  · by_contra hc
    have hc := not_le.1 hc
    have h1 : (t : ℤ) + 1 ≤ -x := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ (t : ℤ) + 1) h1
    nlinarith
  · by_contra hc
    have hc := not_le.1 hc
    have h1 : (t : ℤ) + 1 ≤ x := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ (t : ℤ) + 1) h1
    nlinarith

lemma mem_Nset {t : ℕ} {p : ℤ × ℤ} : p ∈ Nset t ↔ P t p := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    obtain ⟨x, y⟩ := p
    obtain ⟨_, hn⟩ := h
    have hx : x ^ 2 ≤ (t : ℤ) := by nlinarith [sq_nonneg y]
    have hy : y ^ 2 ≤ (t : ℤ) := by nlinarith [sq_nonneg x]
    have bx := bound_of_sq hx
    have bY := bound_of_sq hy
    simp only [inBox, Finset.mem_product, Finset.mem_Icc]
    exact ⟨bx, bY⟩

/-! ### Part (b): the label injection on the quadrant x>0, y≥0 -/

/-- the paper's label L = u²+u+v+1 with u = (x+y−1)/2, v = (x−y−1)/2 (exact division for x+y odd) -/
def Lf (x y : ℤ) : ℤ :=
  ((x + y - 1) / 2) ^ 2 + (x + y - 1) / 2 + (x - y - 1) / 2 + 1

lemma Lf_bounds {x y : ℤ} {t : ℕ} (hx : 0 < x) (hy : 0 ≤ y) (ho : (x + y) % 2 = 1)
    (hn : x ^ 2 + y ^ 2 ≤ (t : ℤ)) : 1 ≤ Lf x y ∧ 2 * Lf x y ≤ (t : ℤ) + 1 := by
  unfold Lf
  obtain ⟨u, hu⟩ : ∃ u, u = (x + y - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (x - y - 1) / 2 := ⟨_, rfl⟩
  rw [← hu, ← hv]
  have hb : 0 ≤ u ∧ -u ≤ v ∧ v ≤ u := by omega
  have hx' : x = u + v + 1 := by omega
  have hy' : y = u - v := by omega
  rw [hx', hy'] at hn
  constructor
  · nlinarith [sq_nonneg u, hb.1, hb.2.1]
  · nlinarith [sq_nonneg v]

lemma Lf_inj {x1 y1 x2 y2 : ℤ} (hx1 : 0 < x1) (hy1 : 0 ≤ y1) (ho1 : (x1 + y1) % 2 = 1)
    (hx2 : 0 < x2) (hy2 : 0 ≤ y2) (ho2 : (x2 + y2) % 2 = 1)
    (h : Lf x1 y1 = Lf x2 y2) : x1 = x2 ∧ y1 = y2 := by
  unfold Lf at h
  obtain ⟨u1, hu1⟩ : ∃ u, u = (x1 + y1 - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨v1, hv1⟩ : ∃ v, v = (x1 - y1 - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u, u = (x2 + y2 - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v, v = (x2 - y2 - 1) / 2 := ⟨_, rfl⟩
  rw [← hu1, ← hv1, ← hu2, ← hv2] at h
  have hb1 : 0 ≤ u1 ∧ -u1 ≤ v1 ∧ v1 ≤ u1 := by omega
  have hb2 : 0 ≤ u2 ∧ -u2 ≤ v2 ∧ v2 ≤ u2 := by omega
  rcases lt_trichotomy u1 u2 with hlt | heq | hgt
  · exfalso
    have h1 : u1 + 1 ≤ u2 := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ u1 + 1) h1
    nlinarith [hb1.2.2, hb2.2.1]
  · subst heq
    have hv : v1 = v2 := by linarith
    omega
  · exfalso
    have h1 : u2 + 1 ≤ u1 := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ u2 + 1) h1
    nlinarith [hb2.2.2, hb1.2.1]

def qA (p : ℤ × ℤ) : Prop := 0 < p.1 ∧ 0 ≤ p.2

noncomputable def Aset (t : ℕ) : Finset (ℤ × ℤ) := (Nset t).filter qA

lemma quarter_card (t : ℕ) : 2 * (Aset t).card ≤ t + 1 := by
  have key : (Aset t).card ≤ (Finset.Icc 1 ((t + 1) / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (Lf p.1 p.2).toNat) ?_ ?_
    · intro p hp
      simp only [Aset, Finset.mem_coe, Finset.mem_filter, mem_Nset, P, qA] at hp
      obtain ⟨⟨ho, hn⟩, hx, hy⟩ := hp
      obtain ⟨b1, b2⟩ := Lf_bounds hx hy ho hn
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    · intro p hp q hq hpq
      simp only [Aset, Finset.mem_coe, Finset.mem_filter, mem_Nset, P, qA] at hp hq
      obtain ⟨⟨ho1, hn1⟩, hx1, hy1⟩ := hp
      obtain ⟨⟨ho2, hn2⟩, hx2, hy2⟩ := hq
      obtain ⟨b1, _⟩ := Lf_bounds hx1 hy1 ho1 hn1
      obtain ⟨b2, _⟩ := Lf_bounds hx2 hy2 ho2 hn2
      have hL : Lf p.1 p.2 = Lf q.1 q.2 := by
        simp only at hpq
        omega
      obtain ⟨e1, e2⟩ := Lf_inj hx1 hy1 ho1 hx2 hy2 ho2 hL
      exact Prod.ext e1 e2
  rw [Nat.card_Icc] at key
  omega

/-! ### Part (a): the quarter-turn gives N_mix = 4 * #A -/

def quad (p : ℤ × ℤ) : ℕ :=
  if 0 < p.1 ∧ 0 ≤ p.2 then 0
  else if p.1 ≤ 0 ∧ 0 < p.2 then 1
  else if p.1 < 0 ∧ p.2 ≤ 0 then 2
  else 3

lemma quad_lt (p : ℤ × ℤ) : quad p < 4 := by
  unfold quad
  split_ifs <;> omega

lemma quad_zero (p : ℤ × ℤ) : quad p = 0 ↔ qA p := by
  unfold quad qA
  split_ifs <;> simp_all

lemma quad_rot (x y : ℤ) (hp : (x + y) % 2 = 1) :
    quad (-y, x) = (quad (x, y) + 1) % 4 ∧ quad (y, -x) = (quad (x, y) + 3) % 4 := by
  unfold quad
  dsimp only
  split_ifs <;> omega

/-- quarter-turn and its inverse -/
def rot (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, p.1)
def rotInv (p : ℤ × ℤ) : ℤ × ℤ := (p.2, -p.1)

lemma P_rot {t : ℕ} {p : ℤ × ℤ} (h : P t p) : P t (rot p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨ho, hn⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [rot]; omega
  · simp only [rot] at *
    rw [neg_sq]; linarith

lemma P_rotInv {t : ℕ} {p : ℤ × ℤ} (h : P t p) : P t (rotInv p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨ho, hn⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [rotInv]; omega
  · simp only [rotInv] at *
    rw [neg_sq]; linarith

noncomputable def fib (t i : ℕ) : Finset (ℤ × ℤ) := (Nset t).filter (fun p => quad p = i)

lemma fib_step (t i : ℕ) (hi : i < 4) : (fib t i).card = (fib t ((i + 1) % 4)).card := by
  refine Finset.card_nbij' rot rotInv ?_ ?_ ?_ ?_
  · intro p hp
    simp only [fib, Finset.mem_coe, Finset.mem_filter, mem_Nset] at hp ⊢
    obtain ⟨hP, hq⟩ := hp
    refine ⟨P_rot hP, ?_⟩
    obtain ⟨x, y⟩ := p
    have := (quad_rot x y hP.1).1
    simp only [rot]
    omega
  · intro p hp
    simp only [fib, Finset.mem_coe, Finset.mem_filter, mem_Nset] at hp ⊢
    obtain ⟨hP, hq⟩ := hp
    refine ⟨P_rotInv hP, ?_⟩
    obtain ⟨x, y⟩ := p
    have := (quad_rot x y hP.1).2
    simp only [rotInv]
    omega
  · intro p _
    obtain ⟨x, y⟩ := p
    simp [rot, rotInv]
  · intro p _
    obtain ⟨x, y⟩ := p
    simp [rot, rotInv]

lemma Nmix_eq (t : ℕ) : Nmix t = 4 * (Aset t).card := by
  have hsum : (Nset t).card = ∑ i ∈ Finset.range 4, (fib t i).card := by
    unfold fib
    exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_range.2 (quad_lt p))
  have h01 := fib_step t 0 (by norm_num)
  have h12 := fib_step t 1 (by norm_num)
  have h23 := fib_step t 2 (by norm_num)
  have hA : (fib t 0) = Aset t := by
    unfold fib Aset
    exact Finset.filter_congr (fun p _ => quad_zero p)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  norm_num at h01 h12 h23
  unfold Nmix
  rw [hsum, ← hA]
  omega

/-- Lemma 4.1 (for integer t). -/
theorem Nmix_le (t : ℕ) : Nmix t ≤ 2 * (t + 1) := by
  have h1 := Nmix_eq t
  have h2 := quarter_card t
  omega

/-! ### Real cutoffs: N_mix(t) = N_mix(⌊t⌋) for t ≥ 0

Lemma 4.2 applies Lemma 4.1 at the real cutoff t = n/p², so the integer version alone is not
enough. UNTESTED in Lean when written. -/

/-- the real-cutoff condition: x+y odd and x²+y² ≤ t, with t a real number -/
def PR (t : ℝ) (p : ℤ × ℤ) : Prop := (p.1 + p.2) % 2 = 1 ∧ ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℝ) ≤ t

lemma PR_iff {t : ℝ} (ht : 0 ≤ t) (p : ℤ × ℤ) : PR t p ↔ P ⌊t⌋₊ p := by
  obtain ⟨x, y⟩ := p
  unfold PR P
  dsimp only
  constructor
  · rintro ⟨ho, hn⟩
    refine ⟨ho, ?_⟩
    have h0 : (0 : ℤ) ≤ x ^ 2 + y ^ 2 := by positivity
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hk] at hn ⊢
    have hk' : k ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast hn)
    exact_mod_cast hk'
  · rintro ⟨ho, hn⟩
    refine ⟨ho, ?_⟩
    have h1 : ((x ^ 2 + y ^ 2 : ℤ) : ℝ) ≤ ((⌊t⌋₊ : ℤ) : ℝ) := by exact_mod_cast hn
    have h2 : ((⌊t⌋₊ : ℤ) : ℝ) = (⌊t⌋₊ : ℝ) := by simp
    linarith [Nat.floor_le ht]

theorem NmixR_floor (t : ℝ) (ht : 0 ≤ t) : {p : ℤ × ℤ | PR t p}.ncard = Nmix ⌊t⌋₊ := by
  have hset : {p : ℤ × ℤ | PR t p} = (↑(Nset ⌊t⌋₊) : Set (ℤ × ℤ)) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_Nset]
    exact PR_iff ht p
  rw [hset, Set.ncard_coe_finset]
  rfl

/-- Lemma 4.1 for real t ≥ 0 -/
theorem NmixR_le (t : ℝ) (ht : 0 ≤ t) : (({p : ℤ × ℤ | PR t p}.ncard : ℕ) : ℝ) ≤ 2 * (t + 1) := by
  rw [NmixR_floor t ht]
  have h : (Nmix ⌊t⌋₊ : ℝ) ≤ 2 * ((⌊t⌋₊ : ℝ) + 1) := by exact_mod_cast Nmix_le ⌊t⌋₊
  linarith [Nat.floor_le ht]

end Section4


/-!
# Lemma 4.2 of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1), CONDITIONAL

STATUS: UNTESTED in Lean when written (no local toolchain). The first part of this file is
Lemma41.lean verbatim (Lemma 4.1, kernel-checked in earlier GitHub runs); the part below is new.

WHAT IS PROVED (once it compiles): for p odd and n, with the explicit hypothesis `hr2`,
      b_p(n) <= 16 * M * (n/(p*p) + 1)          (natural-number division)
      b_p(n) = 0 when n < p*p
and the summed estimate (4.1), with R a real number satisfying 12 n <= R.

HYPOTHESES THAT ARE NOT PROVED HERE (they appear in the theorem statements, not hidden):
* `hr2`: for every integer u with 1 <= u <= n, the number of (a,b) in the box [-n,n]^2 with
  a^2 + b^2 = u is at most 4 * M. In the paper M = M(n) and this is the two-square formula
  r2(u) <= 4 M(n). It is NOT proved here and Mathlib at the project pin has no r2 formula.
* `hR`: 12 n <= R. In the paper R = R(n) = 24 sigma(m) >= 12 n (Jacobi). Not proved here.
Also: the sum on the right of (4.1) is over primes p with p*p <= n only. That is the sum in the
paper restricted to the primes that can occur (the terms with p*p > n vanish, proved below),
so it is no larger than the paper's sum over all p > P. `Rmix`, `bp` are re-declared here
with the same definitions as Sufficiency23.lean (separate file, same text).
-/

namespace Section42
open Section4

noncomputable def Rmix (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1 ∧
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ))

noncomputable def E1 (p n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Rmix n).filter (fun x => (p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1)

noncomputable def E2 (p n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Rmix n).filter (fun x => (p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3)

/-- b_p(n): same as `Sufficiency.bp` -/
noncomputable def bp (p n : ℕ) : ℕ :=
  ((Rmix n).filter (fun x => ((p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1) ∨
    ((p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3))).card

/-- integer points (a,b) of the box [-n,n]^2 with a^2 + b^2 = u -/
noncomputable def R2 (n : ℕ) (u : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun q => q.1 ^ 2 + q.2 ^ 2 = u)

lemma bp_le (p n : ℕ) : bp p n ≤ (E1 p n).card + (E2 p n).card := by
  unfold bp E1 E2
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

lemma mem_Rmix {n : ℕ} {x : Fin 4 → ℤ} :
    x ∈ Rmix n ↔ (∀ i, x i ∈ Finset.Icc (-(n : ℤ)) n) ∧ (x 0 + x 1) % 2 = 1 ∧
      (x 2 + x 3) % 2 = 1 ∧ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ) := by
  unfold Rmix
  rw [Finset.mem_filter, Fintype.mem_piFinset]

def swap (x : Fin 4 → ℤ) : Fin 4 → ℤ := ![x 2, x 3, x 0, x 1]

lemma swap_swap (x : Fin 4 → ℤ) : swap (swap x) = x := by
  funext i
  fin_cases i <;> rfl

lemma swap_mem {n : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ Rmix n) : swap x ∈ Rmix n := by
  rw [mem_Rmix] at hx ⊢
  obtain ⟨hb, h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hb 2
    · exact hb 3
    · exact hb 0
    · exact hb 1
  · simpa [swap] using h2
  · simpa [swap] using h1
  · simp only [swap]
    simp
    linarith

lemma E2_card_le_E1 (p n : ℕ) : (E2 p n).card ≤ (E1 p n).card := by
  refine Finset.card_le_card_of_injOn swap ?_ ?_
  · intro x hx
    have hx' : x ∈ E2 p n := by exact_mod_cast hx
    unfold E2 at hx'
    rw [Finset.mem_filter] at hx'
    change swap x ∈ E1 p n
    unfold E1
    rw [Finset.mem_filter]
    exact ⟨swap_mem hx'.1, by simpa [swap] using hx'.2⟩
  · intro x _ x' _ h
    calc x = swap (swap x) := (swap_swap x).symm
      _ = swap (swap x') := by rw [h]
      _ = x' := swap_swap x'

/-- the pair obtained by dividing the first coordinate pair by p lies in the mixed-parity disk
    of radius^2 n/(p*p) -/
lemma E1_map {p n : ℕ} (hodd : p % 2 = 1) (hp : 0 < p) {x : Fin 4 → ℤ} (hx : x ∈ E1 p n) :
    (x 0 / (p : ℤ), x 1 / (p : ℤ)) ∈ Nset (n / (p * p)) := by
  have hx' := hx
  unfold E1 at hx'
  rw [Finset.mem_filter, mem_Rmix] at hx'
  obtain ⟨⟨hb, h1, h2, h3⟩, d0, d1⟩ := hx'
  have e0 : x 0 = (p : ℤ) * (x 0 / (p : ℤ)) := (Int.mul_ediv_cancel' d0).symm
  have e1 : x 1 = (p : ℤ) * (x 1 / (p : ℤ)) := (Int.mul_ediv_cancel' d1).symm
  generalize x 0 / (p : ℤ) = a0 at e0 ⊢
  generalize x 1 / (p : ℤ) = a1 at e1 ⊢
  have hpz : (p : ℤ) % 2 = 1 := by omega
  rw [mem_Nset]
  unfold P
  dsimp only
  refine ⟨?_, ?_⟩
  · by_contra hne
    have h0 : (a0 + a1) % 2 = 0 := by omega
    obtain ⟨c, hc⟩ : ∃ c, a0 + a1 = 2 * c := ⟨(a0 + a1) / 2, by omega⟩
    have h4 : (p : ℤ) * a0 + (p : ℤ) * a1 = 2 * ((p : ℤ) * c) := by
      rw [← mul_add, hc]; ring
    rw [e0, e1] at h1
    omega
  · have h0 : 0 ≤ a0 ^ 2 + a1 ^ 2 := by positivity
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    rw [ha]
    have hkey : (a : ℤ) * ((p : ℤ) * p) = ((p : ℤ) * a0) ^ 2 + ((p : ℤ) * a1) ^ 2 := by
      rw [← ha]; ring
    rw [e0, e1] at h3
    have hle : (a : ℤ) * ((p : ℤ) * p) ≤ (n : ℤ) := by
      nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    have hmul : a * (p * p) ≤ n := by exact_mod_cast hle
    exact_mod_cast (Nat.le_div_iff_mul_le (Nat.mul_pos hp hp)).2 hmul

lemma fib_data {p n : ℕ} {x : Fin 4 → ℤ} {y : ℤ × ℤ} (hx : x ∈ E1 p n)
    (hxy : (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) : x 0 = p * y.1 ∧ x 1 = p * y.2 := by
  have hx' := hx
  unfold E1 at hx'
  rw [Finset.mem_filter] at hx'
  obtain ⟨_, d0, d1⟩ := hx'
  have e0 : x 0 / (p : ℤ) = y.1 := congrArg Prod.fst hxy
  have e1 : x 1 / (p : ℤ) = y.2 := congrArg Prod.snd hxy
  constructor
  · rw [← e0]; exact (Int.mul_ediv_cancel' d0).symm
  · rw [← e1]; exact (Int.mul_ediv_cancel' d1).symm

/-- the first-pair-divisible-by-p count, using Lemma 4.1 for the divided pair and `hr2` for the
    other pair -/
theorem E1_card_le {p n M : ℕ} (hodd : p % 2 = 1) (hp : 0 < p)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M) :
    (E1 p n).card ≤ 2 * (n / (p * p) + 1) * (4 * M) := by
  have hmap : ∀ x ∈ E1 p n, (x 0 / (p : ℤ), x 1 / (p : ℤ)) ∈ Nset (n / (p * p)) :=
    fun x hx => E1_map hodd hp hx
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin 4 → ℤ => (x 0 / (p : ℤ), x 1 / (p : ℤ)))
    (s := E1 p n) (t := Nset (n / (p * p))) hmap
  have hfib : ∀ y ∈ Nset (n / (p * p)),
      ((E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y)).card ≤ 4 * M := by
    intro y _
    rcases Finset.eq_empty_or_nonempty
      ((E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y)) with hemp | ⟨x₀, hx₀⟩
    · rw [hemp]; simp
    · have key : ∀ x ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y),
          x 2 ^ 2 + x 3 ^ 2 = (n : ℤ) - (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) ∧
          (x 2 + x 3) % 2 = 1 ∧ (∀ i, x i ∈ Finset.Icc (-(n : ℤ)) n) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxE, hxy⟩ := hx
        obtain ⟨f0, f1⟩ := fib_data hxE hxy
        have hxE' := hxE
        unfold E1 at hxE'
        rw [Finset.mem_filter, mem_Rmix] at hxE'
        obtain ⟨⟨hb, h1, h2, h3⟩, d0, d1⟩ := hxE'
        refine ⟨?_, h2, hb⟩
        rw [f0, f1] at h3
        nlinarith [h3]
      obtain ⟨hu_eq, hpar, _⟩ := key x₀ hx₀
      have hu1 : 1 ≤ (n : ℤ) - (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by
        rw [← hu_eq]
        by_contra hlt
        have s2 : x₀ 2 ^ 2 = 0 := by
          nlinarith [sq_nonneg (x₀ 2), sq_nonneg (x₀ 3), not_le.1 hlt]
        have s3 : x₀ 3 ^ 2 = 0 := by
          nlinarith [sq_nonneg (x₀ 2), sq_nonneg (x₀ 3), not_le.1 hlt]
        have hx2 : x₀ 2 = 0 := pow_eq_zero_iff (by norm_num) |>.1 s2
        have hx3 : x₀ 3 = 0 := pow_eq_zero_iff (by norm_num) |>.1 s3
        rw [hx2, hx3] at hpar
        omega
      have hu2 : (n : ℤ) - (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) ≤ n := by
        have : 0 ≤ (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by positivity
        linarith
      refine le_trans (Finset.card_le_card_of_injOn (fun x => (x 2, x 3)) ?_ ?_)
        (hr2 _ hu1 hu2)
      · intro x hx
        have hx' : x ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) := by
          exact_mod_cast hx
        obtain ⟨h1, _, hb⟩ := key x hx'
        change (x 2, x 3) ∈ R2 n _
        unfold R2
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hb 2, hb 3⟩, h1⟩
      · intro x hx x' hx' hxx
        have hxm : x ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) := by
          exact_mod_cast hx
        have hxm' : x' ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) := by
          exact_mod_cast hx'
        rw [Finset.mem_filter] at hxm hxm'
        obtain ⟨a0, a1⟩ := fib_data hxm.1 hxm.2
        obtain ⟨b0, b1⟩ := fib_data hxm'.1 hxm'.2
        have e2 : x 2 = x' 2 := congrArg Prod.fst hxx
        have e3 : x 3 = x' 3 := congrArg Prod.snd hxx
        funext i
        fin_cases i
        · exact a0.trans b0.symm
        · exact a1.trans b1.symm
        · exact e2
        · exact e3
  calc (E1 p n).card
      = ∑ y ∈ Nset (n / (p * p)),
          ((E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y)).card := hsum
    _ ≤ ∑ y ∈ Nset (n / (p * p)), 4 * M := Finset.sum_le_sum hfib
    _ = (Nset (n / (p * p))).card * (4 * M) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * (n / (p * p) + 1)) * (4 * M) :=
        Nat.mul_le_mul_right _ (Nmix_le (n / (p * p)))

lemma E1_empty {p n : ℕ} (hodd : p % 2 = 1) (hp : 0 < p) (hlt : n < p * p) :
    E1 p n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hm := E1_map hodd hp hx
  rw [mem_Nset] at hm
  unfold P at hm
  rw [Nat.div_eq_of_lt hlt] at hm
  obtain ⟨hpar, hb⟩ := hm
  dsimp only at hpar hb
  generalize x 0 / (p : ℤ) = a at hpar hb
  generalize x 1 / (p : ℤ) = b at hpar hb
  have hb0 : a ^ 2 + b ^ 2 ≤ 0 := by exact_mod_cast hb
  have s1 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have s2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have ha : a = 0 := pow_eq_zero_iff (by norm_num) |>.1 s1
  have hb' : b = 0 := pow_eq_zero_iff (by norm_num) |>.1 s2
  rw [ha, hb'] at hpar
  omega

theorem bp_le_16 {p n M : ℕ} (hodd : p % 2 = 1) (hp : 0 < p)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M) :
    bp p n ≤ 16 * M * (n / (p * p) + 1) := by
  have h1 := bp_le p n
  have h2 := E2_card_le_E1 p n
  have h3 := E1_card_le hodd hp hr2
  linarith

theorem bp_zero {p n : ℕ} (hodd : p % 2 = 1) (hp : 0 < p) (hlt : n < p * p) : bp p n = 0 := by
  have h1 := bp_le p n
  have hE1 : (E1 p n).card = 0 := by rw [E1_empty hodd hp hlt]; simp
  have hE2 : (E2 p n).card = 0 := by
    have := E2_card_le_E1 p n
    omega
  omega

/-- (4.1), conditional on `hr2` (two-square count) and `hR` (R >= 12 n). -/
theorem lemma42 (n M P : ℕ) (R : ℝ) (hn : 0 < n)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M)
    (hR : 12 * (n : ℝ) ≤ R) :
    (1 / R) * ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p),
        (bp p n : ℝ)
      ≤ (4 / 3) * M * (∑ p ∈ ((Finset.range (n + 1)).filter
              (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p)).filter (fun p => p * p ≤ n),
              1 / (p : ℝ) ^ 2
          + (((Finset.range (n + 1)).filter
              (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p)).filter (fun p => p * p ≤ n)).card
            / (n : ℝ)) := by
  set Q := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p) with hQ
  set T := Q.filter (fun p => p * p ≤ n) with hT
  have hTQ : T ⊆ Q := Finset.filter_subset _ _
  have hsum : ∑ p ∈ Q, (bp p n : ℝ) = ∑ p ∈ T, (bp p n : ℝ) := by
    symm
    apply Finset.sum_subset hTQ
    intro p hpQ hpT
    have hp := (Finset.mem_filter.1 hpQ).2
    have h4 := hp.2.1
    have hlt : n < p * p := by
      by_contra h
      exact hpT (Finset.mem_filter.2 ⟨hpQ, not_lt.1 h⟩)
    have hodd : p % 2 = 1 := by omega
    have : bp p n = 0 := bp_zero hodd hp.1.pos hlt
    simp [this]
  have hpt : ∀ p ∈ T, (bp p n : ℝ) ≤ 16 * M * ((n : ℝ) * (1 / (p : ℝ) ^ 2) + 1) := by
    intro p hpT
    have hpQ := (Finset.mem_filter.1 hpT).1
    have hp := (Finset.mem_filter.1 hpQ).2
    have h4 := hp.2.1
    have hodd : p % 2 = 1 := by omega
    have hb := bp_le_16 hodd hp.1.pos hr2
    have hcast : (bp p n : ℝ) ≤ 16 * M * (((n / (p * p) : ℕ) : ℝ) + 1) := by
      exact_mod_cast hb
    have hdiv : ((n / (p * p) : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := p * p)
      simpa [pow_two] using this
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hxx : (n : ℝ) / (p : ℝ) ^ 2 = (n : ℝ) * (1 / (p : ℝ) ^ 2) := by ring
    have hmono : 16 * (M : ℝ) * (((n / (p * p) : ℕ) : ℝ) + 1)
        ≤ 16 * (M : ℝ) * ((n : ℝ) * (1 / (p : ℝ) ^ 2) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans hcast hmono
  have hB : ∑ p ∈ T, (bp p n : ℝ)
      ≤ 16 * M * ((n : ℝ) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ)) := by
    calc ∑ p ∈ T, (bp p n : ℝ)
        ≤ ∑ p ∈ T, 16 * (M : ℝ) * ((n : ℝ) * (1 / (p : ℝ) ^ 2) + 1) :=
          Finset.sum_le_sum hpt
      _ = 16 * M * ((n : ℝ) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
  have hS : 0 ≤ ∑ p ∈ T, (bp p n : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  rw [hsum]
  have h1 : 1 / R ≤ 1 / (12 * (n : ℝ)) := one_div_le_one_div_of_le (by positivity) hR
  calc 1 / R * ∑ p ∈ T, (bp p n : ℝ)
      ≤ 1 / (12 * (n : ℝ)) * ∑ p ∈ T, (bp p n : ℝ) := mul_le_mul_of_nonneg_right h1 hS
    _ ≤ 1 / (12 * (n : ℝ)) *
          (16 * M * ((n : ℝ) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (4 / 3) * M * (∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ) / (n : ℝ)) := by
        field_simp
        ring

end Section42



/-!
# Lemma 5.2, estimate (5.2), of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1)

  #{ p prime : p ≡ 3 (mod 4), 3 < p ≤ t }  ≤  2t/15 + 1   for every t ≥ 0.

Stated here as   15 * #{...} ≤ 2 * t + 15   (no division).

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this).
Expect possible compile errors; fix them against what the compiler says.

Method (the paper's mod-60 argument): such a prime is coprime to 60, hence lies in one of the
8 residue classes {7,11,19,23,31,43,47,59} mod 60. Counting integers in those classes up to t
gives the bound; the count is periodic with period 60 and 8 hits per period.

Previously only COMPUTED (checked up to 3,000,000 by script). This file is the proof.
(5.3), the tail sum, is added at the end of this file (also untested when written). (5.4) is added after it (also untested when written).
-/

namespace Section5

/-- the 8 residue classes mod 60 that are 3 mod 4 and coprime to 60 -/
def S : Finset ℕ := {7, 11, 19, 23, 31, 43, 47, 59}

def Pm (n : ℕ) : Prop := n % 60 ∈ S

instance : DecidablePred Pm := fun n => by unfold Pm; infer_instance

lemma count_sixty : Nat.count Pm 60 = 8 := by decide

lemma count_base : ∀ N, N < 60 → 15 * Nat.count Pm N ≤ 2 * N + 13 := by decide

lemma count_shift (M : ℕ) : Nat.count (fun k => Pm (60 + k)) M = Nat.count Pm M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ, ih]
    simp [Pm, Nat.add_mod_left]

lemma count_bound (N : ℕ) : 15 * Nat.count Pm N ≤ 2 * N + 13 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < 60
    · exact count_base N hN
    · obtain ⟨M, rfl⟩ : ∃ M, N = 60 + M := ⟨N - 60, by omega⟩
      have hadd := Nat.count_add (p := Pm) 60 M
      rw [count_shift M, count_sixty] at hadd
      have := ih M (by omega)
      omega

lemma residue_key : ∀ r, r < 60 → r % 4 = 3 → r % 3 ≠ 0 → r % 5 ≠ 0 → r ∈ S := by decide

/-- (5.2): primes p ≡ 3 mod 4 with 3 < p ≤ t number at most 2t/15 + 1. -/
theorem prime_count_bound (t : ℕ) :
    15 * ((Finset.range (t + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p)).card
      ≤ 2 * t + 15 := by
  have hsub : (Finset.range (t + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p)
      ⊆ (Finset.range (t + 1)).filter Pm := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hr, hpr, h4, h3⟩ := hp
    refine ⟨hr, ?_⟩
    have h3d : ¬ 3 ∣ p := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 hd
      omega
    have h5d : ¬ 5 ∣ p := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hpr).1 hd
      omega
    show p % 60 ∈ S
    exact residue_key (p % 60) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) (by omega)
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.range (t + 1)).filter Pm).card = Nat.count Pm (t + 1) :=
    (Nat.count_eq_card_filter_range Pm (t + 1)).symm
  have h3 := count_bound (t + 1)
  omega

/-! ### (5.3): tail sum of 1/p² over primes p ≡ 3 mod 4, p > P

  Σ_{p>P, p≡3 (4)} 1/p²  ≤  2/(15P) + 2/P²     for integers P ≥ 3.

UNTESTED when written. Proof: a purely discrete version of the paper's partial summation.
Let a_k = 1 if k mod 60 ∈ S and 0 otherwise, A(K) = #{1 ≤ k ≤ K : a_k = 1}, and
B_K = A(K) − A(P) − (2/15)(K − P). The count bounds from (5.2) and its lower companion give
B_K ≤ 29/15 ≤ 2, and an induction on K proves
  Σ_{P<k≤K} a_k/k²  ≤  (2/15)(1/P − 1/K) + 2/P² − (2 − B_K)/K².
-/

lemma count_lower (N : ℕ) : 2 * N ≤ 15 * Nat.count Pm N + 16 := by
  have base : ∀ N, N < 60 → 2 * N ≤ 15 * Nat.count Pm N + 16 := by decide
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < 60
    · exact base N hN
    · obtain ⟨M, rfl⟩ : ∃ M, N = 60 + M := ⟨N - 60, by omega⟩
      have hadd := Nat.count_add (p := Pm) 60 M
      rw [count_shift M, count_sixty] at hadd
      have := ih M (by omega)
      omega

/-- A(K) = number of k in [0, K] with k mod 60 ∈ S (0 is never in S, so this counts 1..K) -/
def Acnt (K : ℕ) : ℕ := Nat.count Pm (K + 1)

lemma Acnt_succ (K : ℕ) : Acnt (K + 1) = Acnt K + (if Pm (K + 1) then 1 else 0) := by
  unfold Acnt
  rw [Nat.count_succ]

lemma A_upper (K : ℕ) : (15 : ℝ) * (Acnt K : ℝ) ≤ 2 * K + 15 := by
  have h := count_bound (K + 1)
  unfold Acnt
  have : (15 : ℝ) * (Nat.count Pm (K + 1) : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) + 13 := by exact_mod_cast h
  push_cast at this
  linarith

lemma A_lower (K : ℕ) : 2 * (K : ℝ) ≤ 15 * (Acnt K : ℝ) + 14 := by
  have h := count_lower (K + 1)
  unfold Acnt
  have : 2 * ((K + 1 : ℕ) : ℝ) ≤ 15 * (Nat.count Pm (K + 1) : ℝ) + 16 := by exact_mod_cast h
  push_cast at this
  linarith

noncomputable def Bf (P K : ℕ) : ℝ := (Acnt K : ℝ) - (Acnt P : ℝ) - (2 / 15) * ((K : ℝ) - P)

lemma Bf_le (P K : ℕ) : Bf P K ≤ 2 := by
  unfold Bf
  have h1 := A_upper K
  have h2 := A_lower P
  linarith

lemma Bf_self (P : ℕ) : Bf P P = 0 := by simp [Bf]

lemma Bf_succ (P K : ℕ) :
    Bf P (K + 1) = Bf P K + (if Pm (K + 1) then (1 : ℝ) else 0) - 2 / 15 := by
  by_cases h : Pm (K + 1)
  · simp [Bf, Acnt_succ, h]; ring
  · simp [Bf, Acnt_succ, h]; ring

noncomputable def Ssum (P K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc P K, (if Pm k then (1 : ℝ) else 0) / (k : ℝ) ^ 2

theorem tail_bound (P : ℕ) (hP : 1 ≤ P) :
    ∀ K, P ≤ K → Ssum P K ≤
      (2 / 15) * (1 / (P : ℝ) - 1 / (K : ℝ)) + 2 / (P : ℝ) ^ 2 - (2 - Bf P K) / (K : ℝ) ^ 2 := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have hB := Bf_self P
    simp [Ssum, hB]
  | succ K hK ih =>
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hsum : Ssum P (K + 1) = Ssum P K + (if Pm (K + 1) then (1 : ℝ) else 0) / ((K : ℝ) + 1) ^ 2 := by
      unfold Ssum
      rw [Finset.sum_Ioc_succ_top hK]
      push_cast
      ring
    have hB := Bf_succ P K
    have hb2 := Bf_le P K
    have h1 : 1 / ((K : ℝ) + 1) - 1 / (K : ℝ) + 1 / ((K : ℝ) + 1) ^ 2 ≤ 0 := by
      have e : 1 / ((K : ℝ) + 1) - 1 / (K : ℝ) + 1 / ((K : ℝ) + 1) ^ 2
          = -1 / ((K : ℝ) * ((K : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      rw [e]
      have hpos : 0 < (K : ℝ) * ((K : ℝ) + 1) ^ 2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
    have h2 : 1 / ((K : ℝ) + 1) ^ 2 ≤ 1 / (K : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h3 : 0 ≤ (2 - Bf P K) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hsum, hB]
    push_cast
    -- linarith treats `z / x^2` as one atom, so turn quotients into products with inverse atoms
    have e1 : ∀ z : ℝ, z / ((K : ℝ) + 1) ^ 2 = z * (((K : ℝ) + 1) ^ 2)⁻¹ := fun z => by ring
    have e0 : ∀ z : ℝ, z / (K : ℝ) ^ 2 = z * ((K : ℝ) ^ 2)⁻¹ := fun z => by ring
    simp only [one_div, e1, e0] at ih h1 h3 ⊢
    nlinarith [ih, h1, h3]

lemma prime_in_Pm {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) : Pm p := by
  have h3d : ¬ 3 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
    omega
  have h5d : ¬ 5 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).1 hd
    omega
  show p % 60 ∈ S
  exact residue_key (p % 60) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) (by omega)

/-- (5.3) -/
theorem prime_tail (P : ℕ) (hP : 3 ≤ P) (K : ℕ) :
    ∑ p ∈ (Finset.Ioc P K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2
      ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hrhs : 0 ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 := by positivity
  by_cases hK : P ≤ K
  · have hsub : (Finset.Ioc P K).filter (fun p => p.Prime ∧ p % 4 = 3)
        ⊆ (Finset.Ioc P K).filter Pm := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hI, hpr, h4⟩ := hp
      exact ⟨hI, prime_in_Pm hpr h4 (by have := (Finset.mem_Ioc.1 hI).1; omega)⟩
    have h1 : ∑ p ∈ (Finset.Ioc P K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (Finset.Ioc P K).filter Pm, 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h2 : ∑ p ∈ (Finset.Ioc P K).filter Pm, 1 / (p : ℝ) ^ 2 = Ssum P K := by
      unfold Ssum
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
    have h3 := tail_bound P (by omega) K hK
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have h4 : 0 ≤ (2 - Bf P K) / (K : ℝ) ^ 2 :=
      div_nonneg (by linarith [Bf_le P K]) (by positivity)
    have h5 : 0 < 1 / (K : ℝ) := by positivity
    have h6 : 2 / (15 * (P : ℝ)) = (2 / 15) * (1 / (P : ℝ)) := by field_simp
    rw [h2] at h1
    rw [h6]
    nlinarith [h1, h3, h4, h5]
  · have : (Finset.Ioc P K) = ∅ := by
      ext x; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
    rw [this]
    simpa using hrhs

/-! ### (5.4): 2 Σ_{p ≡ 3 (4)} 1/(p(p−1)) < 21/50

UNTESTED when written, and it depends on `prime_tail` (5.3) compiling first.
Split at 60: the nine primes ≤ 60 are summed exactly; for p > 60, 1/(p(p−1)) ≤ (60/59)/p²,
and (5.3) at P = 60 bounds the rest. This is the paper's own split. -/

def PT (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)

lemma small_primes : ∀ p, p ≤ 60 → p.Prime → p % 4 = 3 →
    p ∈ ({3, 7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ) := by decide

lemma small_sum :
    ∑ p ∈ ({3, 7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      < 21 / 100 - (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) := by
  norm_num [Finset.sum_insert]

theorem five_four (K : ℕ) :
    2 * ∑ p ∈ PT K, 1 / ((p : ℝ) * ((p : ℝ) - 1)) < 21 / 50 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (PT K) (fun p => p ≤ 60)
    (fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1)))
  -- primes up to 60
  have hsmall : ∑ p ∈ (PT K).filter (fun p => p ≤ 60), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ ({3, 7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ), 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [PT, Finset.mem_filter] at hp
      obtain ⟨⟨_, hpr, h4⟩, hle⟩ := hp
      exact small_primes p hle hpr h4
    · intro p hp _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  -- primes above 60
  have hlarge : ∑ p ∈ (PT K).filter (fun p => ¬ p ≤ 60), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) := by
    have hsub : (PT K).filter (fun p => ¬ p ≤ 60)
        ⊆ (Finset.Ioc 60 K).filter (fun p => p.Prime ∧ p % 4 = 3) := by
      intro p hp
      simp only [PT, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨⟨hr, hpr, h4⟩, hle⟩ := hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, by omega⟩, hpr, h4⟩
    have hterm : ∀ p ∈ (PT K).filter (fun p => ¬ p ≤ 60),
        1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (60 / 59) * (1 / (p : ℝ) ^ 2) := by
      intro p hp
      simp only [PT, Finset.mem_filter] at hp
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
    have h2 : ∑ p ∈ (PT K).filter (fun p => ¬ p ≤ 60), 1 / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (Finset.Ioc 60 K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h3 := prime_tail 60 (by norm_num) K
    push_cast at h3
    have h4 : (60 / 59 : ℝ) * ∑ p ∈ (PT K).filter (fun p => ¬ p ≤ 60), 1 / (p : ℝ) ^ 2
        ≤ (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) (by norm_num)
    linarith
  have := small_sum
  linarith

end Section5


/-! ### Prop 6.1, stage 1: the small-prime sum  (UNTESTED, not compiled anywhere)

Lemma52.lean verbatim above; new material below.
`b : ℕ → ℝ` is an ABSTRACT count (later instantiated with Section42.bp p n).
Hypothesis `h31` IS Proposition 3.1 for every prime p ≡ 3 mod 4 with p ≤ P, with
R = R(n) and E = tau(m) sqrt(m) / (3 sigma(m)). It is NOT proved here (Lemma 3.2 is open).
Conclusion is the paper's (6.1) shape: 21/50 + E (2P/15 + 1), via (5.4) = five_four and (5.2) = prime_count_bound. -/

namespace Section61

open Section5

theorem small_primes_sum (b : ℕ → ℝ) (P : ℕ) (R E : ℝ) (hR : 0 < R) (hE : 0 ≤ E)
    (h31 : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ P →
      b p / R ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) + (if 3 < p then E else 0)) :
    (1 / R) * ∑ p ∈ PT P, b p ≤ 21 / 50 + E * (2 * (P : ℝ) / 15 + 1) := by
  have h1 : (1 / R) * ∑ p ∈ PT P, b p = ∑ p ∈ PT P, b p / R := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h2 : ∑ p ∈ PT P, b p / R
      ≤ ∑ p ∈ PT P, (2 / ((p : ℝ) * ((p : ℝ) - 1)) + (if 3 < p then E else 0)) := by
    apply Finset.sum_le_sum
    intro p hp
    simp only [PT, Finset.mem_filter, Finset.mem_range] at hp
    exact h31 p hp.2.1 hp.2.2 (by omega)
  have e1 : ∑ p ∈ PT P, 2 / ((p : ℝ) * ((p : ℝ) - 1))
      = 2 * ∑ p ∈ PT P, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have e2 : ∑ p ∈ PT P, (if 3 < p then E else 0)
      = E * (((PT P).filter (fun p => 3 < p)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsub : (PT P).filter (fun p => 3 < p)
      ⊆ (Finset.range (P + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p) := by
    intro p hp
    simp only [PT, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2, hp.2⟩
  have hcard15 : 15 * ((PT P).filter (fun p => 3 < p)).card ≤ 2 * P + 15 :=
    le_trans (Nat.mul_le_mul_left 15 (Finset.card_le_card hsub)) (prime_count_bound P)
  have hcard : (((PT P).filter (fun p => 3 < p)).card : ℝ) ≤ 2 * (P : ℝ) / 15 + 1 := by
    have : (15 : ℝ) * (((PT P).filter (fun p => 3 < p)).card : ℝ) ≤ 2 * (P : ℝ) + 15 := by
      exact_mod_cast hcard15
    linarith
  have h54 := five_four P
  have hEc : E * (((PT P).filter (fun p => 3 < p)).card : ℝ) ≤ E * (2 * (P : ℝ) / 15 + 1) :=
    mul_le_mul_of_nonneg_left hcard hE
  rw [h1]
  calc ∑ p ∈ PT P, b p / R
      ≤ ∑ p ∈ PT P, (2 / ((p : ℝ) * ((p : ℝ) - 1)) + (if 3 < p then E else 0)) := h2
    _ = 2 * ∑ p ∈ PT P, 1 / ((p : ℝ) * ((p : ℝ) - 1))
          + E * (((PT P).filter (fun p => 3 < p)).card : ℝ) := by
        rw [Finset.sum_add_distrib, e1, e2]
    _ ≤ 21 / 50 + E * (2 * (P : ℝ) / 15 + 1) := by linarith

end Section61


/-! ### Prop 6.1, stage 2a: the second bound of Lemma 5.1, M(n) <= (11/5) n^(1/5)
UNTESTED, not compiled anywhere. LocalFactors.lean verbatim above (green in runs #5, #9, #14).

M(n) of the paper = max over 1 <= u <= n of  prod over primes q = 1 mod 4 with q^e || u of (e+1).
Defined here as `Mn n`, via `Mq u`.  Proof shape (no multiplicativity needed):
  (e_q+1)^5 * d_q <= n_q * q^(e_q)            [local_q, from LocalFactors max_q5/13/17/29, large_prime]
  so  Mq(u)^5 * prod d_q <= prod n_q * prod q^(e_q) <= prod n_q * u,
  and  (prod n_q) * 160225 <= 7962624 * (prod d_q)  for every set of primes (16 subsets of {5,13,17,29}),
  with 7962624/160225 = C2^5 < (11/5)^5.
WHAT THIS DOES NOT PROVE: r2(u) <= 4 Mq(u) (the two-square formula, not in Mathlib), nor the
connection to Section42.R2. Those stay hypotheses of the final assembly. -/

namespace Section62

open LocalFactors

def Sq (u : ℕ) : Finset ℕ := u.primeFactors.filter (fun q => q % 4 = 1)

def Mq (u : ℕ) : ℕ := ∏ q ∈ Sq u, (u.factorization q + 1)

def Mn (n : ℕ) : ℕ := (Finset.Icc 1 n).sup Mq

def nq (q : ℕ) : ℕ :=
  if q = 5 then 243 else if q = 13 then 32 else if q = 17 then 32 else if q = 29 then 32 else 1

def dq (q : ℕ) : ℕ :=
  if q = 5 then 25 else if q = 13 then 13 else if q = 17 then 17 else if q = 29 then 29 else 1

def Tq : Finset ℕ := {5, 13, 17, 29}

lemma dq_pos (q : ℕ) : 0 < dq q := by
  unfold dq; split_ifs <;> norm_num

lemma small_q : ∀ q : ℕ, q ≤ 31 → q.Prime → q % 4 = 1 → q = 5 ∨ q = 13 ∨ q = 17 ∨ q = 29 := by
  decide

lemma local_q (q e : ℕ) (hq : q.Prime) (h4 : q % 4 = 1) :
    (e + 1) ^ 5 * dq q ≤ nq q * q ^ e := by
  by_cases h32 : 32 ≤ q
  · have h5 : q ≠ 5 := by omega
    have h13 : q ≠ 13 := by omega
    have h17 : q ≠ 17 := by omega
    have h29 : q ≠ 29 := by omega
    simpa [dq, nq, h5, h13, h17, h29] using large_prime q e h32
  · have hs := small_q q (by omega) hq h4
    rcases hs with rfl | rfl | rfl | rfl
    · simpa [dq, nq] using max_q5 e
    · simpa [dq, nq] using max_q13 e
    · simpa [dq, nq] using max_q17 e
    · simpa [dq, nq] using max_q29 e

lemma ratio_subsets : ∀ t ∈ Tq.powerset,
    (∏ q ∈ t, nq q) * 160225 ≤ 7962624 * ∏ q ∈ t, dq q := by
  decide

lemma prod_nq_dq (s : Finset ℕ) :
    (∏ q ∈ s, nq q) * 160225 ≤ 7962624 * ∏ q ∈ s, dq q := by
  have key : ∀ g : ℕ → ℕ, (∀ q, q ∉ Tq → g q = 1) →
      ∏ q ∈ s, g q = ∏ q ∈ s.filter (fun q => q ∈ Tq), g q := by
    intro g hg
    have h := Finset.prod_filter_mul_prod_filter_not s (fun q => q ∈ Tq) g
    have h1 : ∏ q ∈ s.filter (fun q => ¬ q ∈ Tq), g q = 1 :=
      Finset.prod_eq_one (fun q hq => hg q (Finset.mem_filter.1 hq).2)
    rw [h1, mul_one] at h
    exact h.symm
  have hn : ∀ q, q ∉ Tq → nq q = 1 := by
    intro q hq
    simp only [Tq, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    obtain ⟨h5, h13, h17, h29⟩ := hq
    simp [nq, h5, h13, h17, h29]
  have hd : ∀ q, q ∉ Tq → dq q = 1 := by
    intro q hq
    simp only [Tq, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    obtain ⟨h5, h13, h17, h29⟩ := hq
    simp [dq, h5, h13, h17, h29]
  rw [key nq hn, key dq hd]
  apply ratio_subsets
  rw [Finset.mem_powerset]
  intro q hq
  exact (Finset.mem_filter.1 hq).2

theorem Mq_pow5 (u : ℕ) (hu : 0 < u) : (Mq u) ^ 5 * 160225 ≤ 7962624 * u := by
  have hterm : ∀ q ∈ Sq u, (u.factorization q + 1) ^ 5 * dq q ≤ nq q * q ^ (u.factorization q) := by
    intro q hq
    have hq' := Finset.mem_filter.1 hq
    exact local_q q _ (Nat.prime_of_mem_primeFactors hq'.1) hq'.2
  have hprod : ∏ q ∈ Sq u, ((u.factorization q + 1) ^ 5 * dq q)
      ≤ ∏ q ∈ Sq u, (nq q * q ^ (u.factorization q)) :=
    Finset.prod_le_prod (fun q _ => Nat.zero_le _) hterm
  have hM : (Mq u) ^ 5 = ∏ q ∈ Sq u, (u.factorization q + 1) ^ 5 := by
    unfold Mq
    exact (Finset.prod_pow _ _ _).symm
  have hL : (Mq u) ^ 5 * ∏ q ∈ Sq u, dq q = ∏ q ∈ Sq u, ((u.factorization q + 1) ^ 5 * dq q) := by
    rw [hM, Finset.prod_mul_distrib]
  have hR : ∏ q ∈ Sq u, (nq q * q ^ (u.factorization q))
      = (∏ q ∈ Sq u, nq q) * ∏ q ∈ Sq u, q ^ (u.factorization q) :=
    Finset.prod_mul_distrib
  have hA : (Mq u) ^ 5 * ∏ q ∈ Sq u, dq q
      ≤ (∏ q ∈ Sq u, nq q) * ∏ q ∈ Sq u, q ^ (u.factorization q) := by
    rw [hL, ← hR]; exact hprod
  have hu' : ∏ q ∈ u.primeFactors, q ^ (u.factorization q) = u := by
    have h := Nat.prod_factorization_pow_eq_self hu.ne'
    rwa [Finsupp.prod, Nat.support_factorization] at h
  have hQ : ∏ q ∈ Sq u, q ^ (u.factorization q) ≤ u := by
    have hd := Finset.prod_dvd_prod_of_subset (Sq u) u.primeFactors
      (fun q => q ^ (u.factorization q)) (by unfold Sq; exact Finset.filter_subset _ _)
    rw [hu'] at hd
    exact Nat.le_of_dvd hu hd
  have hDpos : 0 < ∏ q ∈ Sq u, dq q := Finset.prod_pos (fun q _ => dq_pos q)
  have hND := prod_nq_dq (Sq u)
  have hfin : (Mq u) ^ 5 * 160225 * ∏ q ∈ Sq u, dq q ≤ 7962624 * u * ∏ q ∈ Sq u, dq q := by
    calc (Mq u) ^ 5 * 160225 * ∏ q ∈ Sq u, dq q
        = ((Mq u) ^ 5 * ∏ q ∈ Sq u, dq q) * 160225 := by ring
      _ ≤ ((∏ q ∈ Sq u, nq q) * ∏ q ∈ Sq u, q ^ (u.factorization q)) * 160225 :=
          Nat.mul_le_mul_right _ hA
      _ ≤ ((∏ q ∈ Sq u, nq q) * u) * 160225 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQ)
      _ = u * ((∏ q ∈ Sq u, nq q) * 160225) := by ring
      _ ≤ u * (7962624 * ∏ q ∈ Sq u, dq q) := Nat.mul_le_mul_left _ hND
      _ = 7962624 * u * ∏ q ∈ Sq u, dq q := by ring
  exact Nat.le_of_mul_le_mul_right hfin hDpos

theorem Mq_le (u : ℕ) (hu : 0 < u) (n : ℕ) (hun : u ≤ n) :
    (Mq u : ℝ) ≤ (11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5) := by
  have h := Mq_pow5 u hu
  have hR : ((Mq u : ℝ)) ^ 5 * 160225 ≤ 7962624 * (u : ℝ) := by exact_mod_cast h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hu hun
  have huR : (u : ℝ) ≤ (n : ℝ) := by exact_mod_cast hun
  have hX : 0 ≤ (Mq u : ℝ) := by positivity
  have hY : 0 ≤ (11 / 5 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 5) := by positivity
  have h5 : ((n : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  have hy5 : ((11 / 5 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = (11 / 5 : ℝ) ^ 5 * (n : ℝ) := by
    rw [mul_pow, h5]
  have hq : ((Mq u : ℝ)) ^ 5 ≤ (7962624 / 160225 : ℝ) * (u : ℝ) := by
    have h2 : (0 : ℝ) < 160225 := by norm_num
    rw [div_mul_eq_mul_div, le_div_iff₀ h2]
    linarith
  have hle : ((Mq u : ℝ)) ^ 5 ≤ ((11 / 5 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 := by
    rw [hy5]
    calc ((Mq u : ℝ)) ^ 5 ≤ (7962624 / 160225 : ℝ) * (u : ℝ) := hq
      _ ≤ (7962624 / 160225 : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left huR (by norm_num)
      _ ≤ (11 / 5 : ℝ) ^ 5 * (n : ℝ) := mul_le_mul_of_nonneg_right (by norm_num) hnR.le
  exact (pow_le_pow_iff_left₀ hX hY (by norm_num)).1 hle

theorem Mn_le (n : ℕ) : (Mn n : ℝ) ≤ (11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5) := by
  by_cases hn : n = 0
  · subst hn
    have h0 : Mn 0 = 0 := by simp [Mn]
    rw [h0]
    simp only [Nat.cast_zero]
    positivity
  · obtain ⟨u, hu, hsup⟩ := Finset.exists_mem_eq_sup (Finset.Icc 1 n)
      ⟨1, Finset.mem_Icc.2 ⟨le_refl 1, by omega⟩⟩ Mq
    have hu' := Finset.mem_Icc.1 hu
    unfold Mn
    rw [hsup]
    exact Mq_le u (by omega) n hu'.2

end Section62


/-! ### Prop 6.1, stage 2b: the large-prime bound, shape of (6.2)
UNTESTED, not compiled anywhere. Lemma42.lean verbatim, then Lemma52.lean verbatim (its `import` line
dropped), then the new material below.

Combines Section42.lemma42 (conditional on hr2, hR) with (5.3) = Section5.prime_tail and
(5.2) = Section5.prime_count_bound. Hypotheses carried, NOT proved here:
  hr2 : r2(u) <= 4 M for 1 <= u <= n      (two-square formula, not in Mathlib)
  hR  : 12 n <= R                           (Jacobi: R = 24 sigma(m) >= 12 n)
  hM  : M <= (11/5) n^(1/5)                 (Section62.Mn_le gives this for M = Mn n; kept abstract here)
Conclusion has the paper's shape  (4/3) * M-bound * (2/(15P) + 2/P^2 + (2 sqrt n/15 + 1)/n). -/

namespace Section62b

open Section42 Section5

def Qs (n P : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p)

def Ts (n P : ℕ) : Finset ℕ := (Qs n P).filter (fun p => p * p ≤ n)

theorem large_primes (n P M : ℕ) (R : ℝ) (hn : 0 < n) (hP : 3 ≤ P)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M)
    (hR : 12 * (n : ℝ) ≤ R)
    (hM : (M : ℝ) ≤ (11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) :
    (1 / R) * ∑ p ∈ Qs n P, (bp p n : ℝ)
      ≤ (4 / 3) * ((11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) *
          (2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ)) := by
  have h42 : (1 / R) * ∑ p ∈ Qs n P, (bp p n : ℝ)
      ≤ (4 / 3) * M * (∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ)) :=
    Section42.lemma42 n M P R hn hr2 hR
  -- (5.3) on T
  have hsub : Ts n P ⊆ (Finset.Ioc P n).filter (fun p => p.Prime ∧ p % 4 = 3) := by
    intro p hp
    simp only [Ts, Qs, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hlt, hpr, h4, hPp⟩, _⟩ := hp
    exact ⟨⟨hPp, by omega⟩, hpr, h4⟩
  have hS : ∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
      (prime_tail P hP n)
  -- (5.2) on T, at t = Nat.sqrt n
  have hsubc : Ts n P ⊆
      (Finset.range (Nat.sqrt n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p) := by
    intro p hp
    simp only [Ts, Qs, Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨⟨hlt, hpr, h4, hPp⟩, hpp⟩ := hp
    have hsq := Nat.le_sqrt.2 hpp
    exact ⟨by omega, hpr, h4, by omega⟩
  have hc15 : 15 * (Ts n P).card ≤ 2 * Nat.sqrt n + 15 :=
    le_trans (Nat.mul_le_mul_left 15 (Finset.card_le_card hsubc)) (prime_count_bound (Nat.sqrt n))
  have hcR : ((Ts n P).card : ℝ) ≤ 2 * Real.sqrt n / 15 + 1 := by
    have h1 : (15 : ℝ) * ((Ts n P).card : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) + 15 := by
      exact_mod_cast hc15
    have h2 : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiv : ((Ts n P).card : ℝ) / (n : ℝ) ≤ (2 * Real.sqrt n / 15 + 1) / (n : ℝ) :=
    div_le_div_of_nonneg_right hcR hnR.le
  have hUV : ∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ)
      ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ) := by
    linarith
  have hU0 : 0 ≤ ∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ) := by positivity
  have hMb : 0 ≤ (11 / 5 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 5) := by positivity
  calc (1 / R) * ∑ p ∈ Qs n P, (bp p n : ℝ)
      ≤ (4 / 3) * M * (∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ)) := h42
    _ ≤ (4 / 3) * ((11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) *
          (2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hUV hU0
          (mul_nonneg (by norm_num) hMb)

end Section62b



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



/-! ### Prop 6.1, stage 3b: the core assembly (UNTESTED, not compiled anywhere)

Everything above this line is the earlier files merged once each (LocalFactors, Section51 = Lemma51,
Section4/42 = Lemma41/42, Section5 = Lemma52, Section61, Section62, Section62b, Section63).

`prop61_core` states: for m with all prime factors = 3 mod 4 and n = 2m >= 64^4, the sum of b_p(n)/R(n)
over ALL primes p = 3 mod 4 up to n is < 2/3, R = 24 sigma(m).
HYPOTHESES CARRIED, none proved here:
  h31 : Prop 3.1 for p <= P  (needs Lemma 3.2: Jacquet-Langlands + weight-2 Ramanujan-Petersson, OPEN)
  hr2 : r2(u) <= 4 Mn(n) for 1 <= u <= n  (two-square formula, not in Mathlib)
It DERIVES (from earlier green pieces): 12 n <= R from sigma(m) >= m; M-bound from Mn_le; E <= (49/50)/u^6 from
lemma51_first; the split of the prime sum at P; the arithmetic. It does NOT prove Jacobi's R(n) = 24 sigma(m),
|Rmix| = (2/3) R, or connect Section42.bp to Sufficiency.bp; so it does NOT yet conclude n in A + A. -/

namespace Section63b

open Section5 Section42 Section62 Section62b Section61 Section63

noncomputable def Pn (n : ℕ) : ℕ := ⌊2 * (n : ℝ) ^ ((1 : ℝ) / 4)⌋₊

theorem prop61_core (m : ℕ) (hm : 0 < m)
    (hmod : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3)
    (hn64 : 64 ^ 4 ≤ 2 * m)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ ((2 * m : ℕ) : ℤ) → (R2 (2 * m) u).card ≤ 4 * Mn (2 * m))
    (h31 : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ Pn (2 * m) →
      (bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
        ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
          + (if 3 < p then (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ))
             else 0)) :
    (1 / (24 * (Section51.sig m : ℝ))) * ∑ p ∈ PT (2 * m), (bp p (2 * m) : ℝ) < 2 / 3 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 * m := ⟨_, rfl⟩
  rw [← hn] at hn64 hr2 h31 ⊢
  have hnpos : 0 < n := by omega
  have hnR : (n : ℝ) = 2 * (m : ℝ) := by rw [hn]; push_cast; ring
  have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- u = n^(1/20)
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = (n : ℝ) ^ ((1 : ℝ) / 20) := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  have hpow : ∀ k : ℕ, u ^ k = (n : ℝ) ^ ((k : ℝ) / 20) := by
    intro k
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hnRpos.le]
    congr 1
    ring
  have hu20 : u ^ 20 = (n : ℝ) := by
    rw [hpow 20]; norm_num
  have hu4 : u ^ 4 = (n : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [hpow 4]; congr 1; norm_num
  have hu5 : u ^ 5 = (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hpow 5]; congr 1; norm_num
  have hsqrtn : Real.sqrt (n : ℝ) = u ^ 10 := by
    rw [← hu20, show u ^ 20 = (u ^ 10) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hX : (64 : ℝ) ≤ u ^ 5 := by
    have h1 : (64 : ℝ) ^ 4 ≤ (u ^ 5) ^ 4 := by
      have : (u ^ 5) ^ 4 = (n : ℝ) := by rw [← hu20]; ring
      rw [this]
      exact_mod_cast hn64
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).1 h1
  -- P
  have hP : Pn n = ⌊2 * u ^ 5⌋₊ := by unfold Pn; rw [hu5]
  have hP2 : (Pn n : ℝ) ≤ 2 * u ^ 5 := by rw [hP]; exact Nat.floor_le (by positivity)
  have hP1 : 2 * u ^ 5 - 1 ≤ (Pn n : ℝ) := by
    rw [hP]
    have := Nat.lt_floor_add_one (2 * u ^ 5)
    linarith
  have hP127 : (127 : ℝ) ≤ (Pn n : ℝ) := by linarith
  have hP3 : 3 ≤ Pn n := by
    have : (127 : ℕ) ≤ Pn n := by exact_mod_cast hP127
    omega
  have hPn : Pn n ≤ n := by
    have h3 : (64 : ℝ) ^ 3 ≤ (u ^ 5) ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
    have h2 : (2 : ℝ) ≤ (u ^ 5) ^ 3 := by norm_num at h3; linarith
    have hpos : (0 : ℝ) ≤ u ^ 5 := by positivity
    have h15 : 2 * u ^ 5 ≤ u ^ 20 := by
      have : u ^ 20 = u ^ 5 * (u ^ 5) ^ 3 := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left h2 hpos]
    have : (Pn n : ℝ) ≤ (n : ℝ) := by rw [← hu20]; linarith
    exact_mod_cast this
  -- R
  have hsigge : m ≤ Section51.sig m := Section51.sig_ge hm
  have hsigR : (m : ℝ) ≤ (Section51.sig m : ℝ) := by exact_mod_cast hsigge
  have hsigpos : (0 : ℝ) < (Section51.sig m : ℝ) := by linarith
  have hRpos : (0 : ℝ) < 24 * (Section51.sig m : ℝ) := by linarith
  have hR12 : 12 * (n : ℝ) ≤ 24 * (Section51.sig m : ℝ) := by rw [hnR]; linarith
  -- E
  set E : ℝ := (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ)) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hsqm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hEA : E * (3 * Real.sqrt (m : ℝ))
      = (Section51.tau m : ℝ) * (m : ℝ) / (Section51.sig m : ℝ) := by
    calc E * (3 * Real.sqrt (m : ℝ))
        = (Section51.tau m : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ))
            / (Section51.sig m : ℝ) := by
          rw [hEdef]; field_simp
      _ = (Section51.tau m : ℝ) * (m : ℝ) / (Section51.sig m : ℝ) := by rw [hsqm]
  have hA : (Section51.tau m : ℝ) * (m : ℝ) / (Section51.sig m : ℝ)
      ≤ (23 / 10) * (m : ℝ) ^ ((1 : ℝ) / 5) := Section51.lemma51_first m hm hmod
  have hmu : (m : ℝ) = u ^ 20 / 2 := by
    have h := hnR
    rw [← hu20] at h
    linarith
  have h20 : (0 : ℝ) < u ^ 20 := by positivity
  have hm15 : (m : ℝ) ^ ((1 : ℝ) / 5) ≤ (9 / 10) * u ^ 4 := by
    have hX0 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 5) := by positivity
    have hY0 : 0 ≤ (9 / 10 : ℝ) * u ^ 4 := by positivity
    have h5 : ((m : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 = (m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
      norm_num
    have hle : ((m : ℝ) ^ ((1 : ℝ) / 5)) ^ 5 ≤ ((9 / 10 : ℝ) * u ^ 4) ^ 5 := by
      rw [h5, mul_pow, hmu, show (u ^ 4) ^ 5 = u ^ 20 by ring]
      nlinarith [h20]
    exact (pow_le_pow_iff_left₀ hX0 hY0 (by norm_num : (5 : ℕ) ≠ 0)).1 hle
  have hsqlow : (50 / 71 : ℝ) * u ^ 10 ≤ Real.sqrt (m : ℝ) := by
    have hle : ((50 / 71 : ℝ) * u ^ 10) ^ 2 ≤ (m : ℝ) := by
      rw [hmu, mul_pow, show (u ^ 10) ^ 2 = u ^ 20 by ring]
      nlinarith [h20]
    calc (50 / 71 : ℝ) * u ^ 10 = Real.sqrt (((50 / 71 : ℝ) * u ^ 10) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hle
  have hy : (E * u ^ 6 * (150 / 71)) * u ^ 4 ≤ (207 / 100) * u ^ 4 := by
    calc (E * u ^ 6 * (150 / 71)) * u ^ 4
        = E * (3 * ((50 / 71 : ℝ) * u ^ 10)) := by ring
      _ ≤ E * (3 * Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hE0
      _ = (Section51.tau m : ℝ) * (m : ℝ) / (Section51.sig m : ℝ) := hEA
      _ ≤ (23 / 10) * (m : ℝ) ^ ((1 : ℝ) / 5) := hA
      _ ≤ (23 / 10) * ((9 / 10) * u ^ 4) := by linarith
      _ = (207 / 100) * u ^ 4 := by ring
  have hy2 : E * u ^ 6 * (150 / 71) ≤ 207 / 100 := le_of_mul_le_mul_right hy (pow_pos hu 4)
  have hE : E ≤ (49 / 50) / u ^ 6 := by
    rw [le_div_iff₀ (pow_pos hu 6)]
    linarith
  -- small primes
  have hS : (1 / (24 * (Section51.sig m : ℝ))) * ∑ p ∈ PT (Pn n), (bp p n : ℝ)
      ≤ 21 / 50 + E * (2 * (Pn n : ℝ) / 15 + 1) :=
    small_primes_sum (fun p => (bp p n : ℝ)) (Pn n) (24 * (Section51.sig m : ℝ)) E hRpos hE0
      (fun p hp h4 hle => h31 p hp h4 hle)
  -- large primes
  have hL0 := large_primes n (Pn n) (Mn n) (24 * (Section51.sig m : ℝ)) hnpos hP3 hr2 hR12
    (Mn_le n)
  rw [← hu4, hsqrtn, ← hu20] at hL0
  -- arithmetic
  have hfin := final_arith u (Pn n) E hu hX hP1 hP2 hE0 hE
  -- split the prime sum at P
  have hf1 : (PT n).filter (fun p => p ≤ Pn n) = PT (Pn n) := by
    ext p
    simp only [PT, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hlt, hpr, h4⟩, hle⟩
      exact ⟨by omega, hpr, h4⟩
    · rintro ⟨hlt, hpr, h4⟩
      exact ⟨⟨by omega, hpr, h4⟩, by omega⟩
  have hf2 : (PT n).filter (fun p => ¬ p ≤ Pn n) = Qs n (Pn n) := by
    ext p
    simp only [PT, Qs, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hlt, hpr, h4⟩, hnle⟩
      exact ⟨hlt, hpr, h4, by omega⟩
    · rintro ⟨hlt, hpr, h4, hP⟩
      exact ⟨⟨hlt, hpr, h4⟩, by omega⟩
  have hsplit : ∑ p ∈ PT n, (bp p n : ℝ)
      = ∑ p ∈ PT (Pn n), (bp p n : ℝ) + ∑ p ∈ Qs n (Pn n), (bp p n : ℝ) := by
    have h := Finset.sum_filter_add_sum_filter_not (PT n) (fun p => p ≤ Pn n)
      (fun p => (bp p n : ℝ))
    simp only [hf1, hf2] at h
    exact h.symm
  rw [hsplit, mul_add]
  linarith [hS, hL0, hfin]

end Section63b

#print axioms Section63b.prop61_core


/-!
# (2.3), sufficiency step, of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1)

Paper: for n = 2m, let Rmix(n) be the integer solutions of x0²+x1²+x2²+x3² = n in which each of
(x0,x1) and (x2,x3) has opposite parity (x0+x1 odd, x2+x3 odd). For a prime p ≡ 3 (mod 4), let
b_p(n) count the elements of Rmix(n) with (p | x0 and p | x1) or (p | x2 and p | x3).
Then
      Σ_p b_p(n) < |Rmix(n)|   implies   n = a + b with a, b in A,
where A = positive integers all of whose prime factors are ≡ 1 mod 4.

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this).

What this proves: ONLY the implication above (the pigeonhole / "-1 is a nonresidue" step).
It does NOT prove |Rmix(n)| = (2/3)·R(n), nor R(n) = 24σ(m), nor any bound on Σ b_p; those are
(2.2) (FourSquaresMixed.lean), Jacobi's formula (open), and Prop 3.1/Lemma 4.2/Prop 6.1.
The sum here runs over primes p ≡ 3 mod 4 with p ≤ n, which suffices because every prime
factor of x0²+x1² ≤ n is at most n.
-/

namespace Sufficiency

/-- the paper's set A: positive integers all of whose prime factors are 1 mod 4 (1 allowed);
    same definition as `Euler1747.EulerGood` -/
def Good (a : ℕ) : Prop := 0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p % 4 = 1

/-- a prime ≡ 3 mod 4 dividing a sum of two squares divides both -/
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

noncomputable def Rmix (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1 ∧
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ))

noncomputable def Eset (p n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Rmix n).filter (fun x => ((p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1) ∨ ((p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3))

/-- b_p(n) -/
noncomputable def bp (p n : ℕ) : ℕ := (Eset p n).card

/-- a pair of opposite parity, with no prime ≡ 3 mod 4 dividing both coordinates, gives a good number -/
lemma good_of_pair {x y : ℤ} {n : ℕ} (hodd : (x + y) % 2 = 1) (hle : x ^ 2 + y ^ 2 ≤ (n : ℤ))
    (hno : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ n → ¬ ((q : ℤ) ∣ x ∧ (q : ℤ) ∣ y)) :
    Good (x ^ 2 + y ^ 2).toNat := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by
    by_contra hc
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    subst hx; subst hy
    omega
  have hcast : (((x ^ 2 + y ^ 2).toNat : ℕ) : ℤ) = x ^ 2 + y ^ 2 := Int.toNat_of_nonneg hpos.le
  refine ⟨by omega, ?_⟩
  intro q hq hqd
  have hqdz : (q : ℤ) ∣ x ^ 2 + y ^ 2 := by
    rw [← hcast]; exact Int.natCast_dvd_natCast.2 hqd
  -- the number is odd
  have hodd2 : (x ^ 2 + y ^ 2) % 2 = 1 := by
    have : x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 := by omega
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, h2]
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : (2 : ℤ) ∣ x ^ 2 + y ^ 2 := hqdz
    omega
  have hqle : q ≤ n := by
    have : (q : ℤ) ≤ x ^ 2 + y ^ 2 := Int.le_of_dvd hpos hqdz
    have : (q : ℤ) ≤ n := le_trans this hle
    exact_mod_cast this
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    have h2 : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    omega
  rcases hq4 with h | h
  · exact h
  · exact absurd (dvd_of_sq_add hq h x y hqdz) (hno q hq h hqle)

theorem sufficiency (n : ℕ)
    (h : ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3), bp p n
          < (Rmix n).card) :
    ∃ a b : ℕ, Good a ∧ Good b ∧ a + b = n := by
  by_contra hne
  have hcov : Rmix n ⊆
      ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)).biUnion (fun p => Eset p n) := by
    intro x hx
    by_contra hnot
    apply hne
    rw [Finset.mem_biUnion] at hnot
    simp only [not_exists, not_and] at hnot
    have hx' := (Finset.mem_filter.1 hx).2
    obtain ⟨ho1, ho2, hsum⟩ := hx'
    have hno1 : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ n → ¬ ((q : ℤ) ∣ x 0 ∧ (q : ℤ) ∣ x 1) := by
      intro q hq h3 hqn hdiv
      apply hnot q (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq, h3⟩)
      exact Finset.mem_filter.2 ⟨hx, Or.inl hdiv⟩
    have hno2 : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ n → ¬ ((q : ℤ) ∣ x 2 ∧ (q : ℤ) ∣ x 3) := by
      intro q hq h3 hqn hdiv
      apply hnot q (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq, h3⟩)
      exact Finset.mem_filter.2 ⟨hx, Or.inr hdiv⟩
    have hle1 : x 0 ^ 2 + x 1 ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    have hle2 : x 2 ^ 2 + x 3 ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hg1 := good_of_pair ho1 hle1 hno1
    have hg2 := good_of_pair ho2 hle2 hno2
    refine ⟨(x 0 ^ 2 + x 1 ^ 2).toNat, (x 2 ^ 2 + x 3 ^ 2).toNat, hg1, hg2, ?_⟩
    have p1 : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    have p2 : 0 ≤ x 2 ^ 2 + x 3 ^ 2 := by positivity
    omega
  have hcard := Finset.card_le_card hcov
  have hbu := Finset.card_biUnion_le (s := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3))
    (t := fun p => Eset p n)
  unfold bp at h
  omega

end Sufficiency

#print axioms Sufficiency.sufficiency

/-
  FourSquaresMixed.lean   (draft written 2026-11-16 by Claude; UNTESTED. 2026-11-16 first compile gave 2 errors, patched, not re-run)

  Source: equation (2.2) of Howe-Huffman-Kohlmeyer-Kruer, hexagon:2611.00370v1.

  WHAT THIS FILE PROVES, if it compiles:
    For n with n % 4 = 2, let R n be the set of signed, ordered representations
    (x0,x1,x2,x3) in Z^4 with x0^2+x1^2+x2^2+x3^2 = n, and let Rmix be those in which
    x0+x1 is odd and x2+x3 is odd.  Then   3 * |Rmix| = 2 * |R|,   i.e. |Rmix| = (2/3)|R|.

  WHAT THIS FILE DOES NOT PROVE:
    It does NOT prove Jacobi's four-square formula |R n| = 24 sigma(m), and it does NOT say
    anything about |R n| itself; it only relates two counts.  Jacobi's count is not in Mathlib
    (checked in the geometry checkout, Mathlib dated 2026-07-13) and is a separate, larger job.

  Proof idea (the paper's): n = 2 mod 4 forces exactly two coordinates to be odd.  Look at the
  three ways to split the coordinates into two pairs: {01|23}, {02|13}, {03|12}.  An x counts as
  "mixed" for a split when its two odd coordinates lie in different pairs.  Each x is mixed for
  EXACTLY TWO of the three splits, and swapping coordinates shows the three splits have the same
  count.  So 3 * |Rmix| = 2 * |R|.

  Run:  cd ~/Desktop/DM3-lab/euler/lean
        lake env lean EulerLean/FourSquaresMixed.lean
-/

namespace FourSq

/-- Signed ordered representations of `n` as a sum of four squares, as a finite set. -/
noncomputable def R (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => ∑ i, x i ^ 2 = (n : ℤ))

/-- Split {01|23}: both pairs have opposite parity. -/
def S1 (x : Fin 4 → ℤ) : Prop := (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1
/-- Split {02|13}. -/
def S2 (x : Fin 4 → ℤ) : Prop := (x 0 + x 2) % 2 = 1 ∧ (x 1 + x 3) % 2 = 1
/-- Split {03|12}. -/
def S3 (x : Fin 4 → ℤ) : Prop := (x 0 + x 3) % 2 = 1 ∧ (x 1 + x 2) % 2 = 1

instance : DecidablePred S1 := fun x => by unfold S1; infer_instance
instance : DecidablePred S2 := fun x => by unfold S2; infer_instance
instance : DecidablePred S3 := fun x => by unfold S3; infer_instance

theorem sq_mod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
  · subst hk
    have : (2 * k) ^ 2 = 4 * (k ^ 2) := by ring
    rw [this]; omega
  · subst hk
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    rw [this]; omega

/-- Each representation is mixed for exactly two of the three splits. -/
theorem pointwise (n : ℕ) (hn : n % 4 = 2) (x : Fin 4 → ℤ) (hx : x ∈ R n) :
    ((if S1 x then 1 else 0) + (if S2 x then 1 else 0) + (if S3 x then 1 else 0) : ℕ) = 2 := by
  have hs : ∑ i, x i ^ 2 = (n : ℤ) := (Finset.mem_filter.1 hx).2
  rw [Fin.sum_univ_four] at hs
  have h0 := sq_mod_four (x 0)
  have h1 := sq_mod_four (x 1)
  have h2 := sq_mod_four (x 2)
  have h3 := sq_mod_four (x 3)
  unfold S1 S2 S3
  split_ifs <;> omega

/-- Permuting coordinates keeps us inside `R n`. -/
theorem comp_mem_R (σ : Equiv.Perm (Fin 4)) {n : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ R n) :
    (x ∘ σ) ∈ R n := by
  simp only [R, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  obtain ⟨hb, hs⟩ := hx
  refine ⟨fun i => hb (σ i), ?_⟩
  have := Equiv.sum_comp σ (fun i => x i ^ 2)
  simpa [Function.comp] using this.trans hs

theorem comp_involution (σ : Equiv.Perm (Fin 4)) (h2 : ∀ i, σ (σ i) = i) (x : Fin 4 → ℤ) :
    (x ∘ σ) ∘ σ = x := by
  funext i; simp [Function.comp, h2]

/-- If swapping coordinates by an involution `σ` carries `p` to `q`, the two counts agree. -/
theorem card_filter_eq (σ : Equiv.Perm (Fin 4)) (h2 : ∀ i, σ (σ i) = i) (n : ℕ)
    (p q : (Fin 4 → ℤ) → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, q (x ∘ σ) ↔ p x) :
    ((R n).filter p).card = ((R n).filter q).card := by
  have hqp : ∀ x, p (x ∘ σ) ↔ q x := fun x => by
    rw [← hpq (x ∘ σ), comp_involution σ h2 x]
  refine Finset.card_bij' (fun x _ => x ∘ σ) (fun x _ => x ∘ σ) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨comp_mem_R σ hx.1, (hpq x).2 hx.2⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨comp_mem_R σ hx.1, (hqp x).2 hx.2⟩
  · intro x _; exact comp_involution σ h2 x
  · intro x _; exact comp_involution σ h2 x

/-- Equation (2.2) of the paper:  |Rmix| = (2/3) |R|  for n = 2 mod 4. -/
theorem mixed_count (n : ℕ) (hn : n % 4 = 2) :
    3 * ((R n).filter S1).card = 2 * (R n).card := by
  -- swap coordinates 1 and 2:  S2 (x ∘ σ) ↔ S1 x
  have a0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have a1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have a2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have a3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have e12 : ((R n).filter S1).card = ((R n).filter S2).card :=
    card_filter_eq (Equiv.swap 1 2) (fun i => Equiv.swap_apply_self _ _ i) n S1 S2
      (fun x => by simp [S1, S2, Function.comp, a0, a1, a2, a3])
  -- swap coordinates 1 and 3:  S3 (x ∘ σ) ↔ S1 x
  have b0 : Equiv.swap (1 : Fin 4) 3 0 = 0 := by decide
  have b1 : Equiv.swap (1 : Fin 4) 3 1 = 3 := by decide
  have b2 : Equiv.swap (1 : Fin 4) 3 2 = 2 := by decide
  have b3 : Equiv.swap (1 : Fin 4) 3 3 = 1 := by decide
  have e13 : ((R n).filter S1).card = ((R n).filter S3).card :=
    card_filter_eq (Equiv.swap 1 3) (fun i => Equiv.swap_apply_self _ _ i) n S1 S3
      (fun x => by simp only [S1, S3, Function.comp_apply, b0, b1, b2, b3]; omega)
  have hsum : ((R n).filter S1).card + ((R n).filter S2).card + ((R n).filter S3).card
      = 2 * (R n).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun x hx => pointwise n hn x hx)]
    simp [Finset.sum_const, mul_comm]
  omega

/-! Numerical sanity check (NOT in Lean: `R` is noncomputable). Python brute force gave
    3*|Rmix| = 2*|R| for n = 2,6,10,14,18,22; for n = 6 the pair is (|R|, |Rmix|) = (96, 64). -/

end FourSq

#print axioms FourSq.mixed_count

/-! ### Section64: connect prop61_core to Sufficiency.sufficiency (UNTESTED, not compiled anywhere)

PROVES (if it compiles): for odd m with every prime factor = 3 mod 4 and 64^4 <= 2m, and
  hr2, h31   (the same two OPEN hypotheses as prop61_core),
  hJ : 16 sigma(m) <= |Rmix(2m)|   (lower bound; follows from Jacobi + mixed_count, see hJ_of_jacobi),
there are Good a, Good b with a + b = 2m.
DOES NOT PROVE: h31 (Lemma 3.2 open), hr2 (two-square count), Jacobi's |R(n)| = 24 sigma(m). -/

namespace Section64

lemma rmix_eq (n : ℕ) : Section42.Rmix n = Sufficiency.Rmix n := by
  first
  | rfl
  | (ext x; simp [Section42.Rmix, Sufficiency.Rmix])

lemma bp_eq (p n : ℕ) : Section42.bp p n = Sufficiency.bp p n := by
  first
  | rfl
  | (unfold Section42.bp Sufficiency.bp Sufficiency.Eset; rw [rmix_eq])

lemma rmix_eq_four (n : ℕ) : Sufficiency.Rmix n = (FourSq.R n).filter FourSq.S1 := by
  ext x
  simp only [Sufficiency.Rmix, FourSq.R, Finset.mem_filter, Fin.sum_univ_four, FourSq.S1]
  tauto

/-- From Jacobi's count (a HYPOTHESIS here) and (2.2): |Rmix(2m)| = 16 sigma(m); only the lower bound is returned. -/
lemma hJ_of_jacobi (m : ℕ) (hm : m % 2 = 1)
    (hjac : (FourSq.R (2 * m)).card = 24 * Section51.sig m) :
    16 * Section51.sig m ≤ (Sufficiency.Rmix (2 * m)).card := by
  have h := FourSq.mixed_count (2 * m) (by omega)
  rw [rmix_eq_four]
  omega

theorem euler_conditional (m : ℕ) (hm : m % 2 = 1)
    (hmod : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3)
    (hn64 : 64 ^ 4 ≤ 2 * m)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ ((2 * m : ℕ) : ℤ) →
      (Section42.R2 (2 * m) u).card ≤ 4 * Section62.Mn (2 * m))
    (h31 : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ Section63b.Pn (2 * m) →
      (Section42.bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
        ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
          + (if 3 < p then (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ))
             else 0))
    (hJ : 16 * Section51.sig m ≤ (Sufficiency.Rmix (2 * m)).card) :
    ∃ a b : ℕ, Sufficiency.Good a ∧ Sufficiency.Good b ∧ a + b = 2 * m := by
  have hm0 : 0 < m := by omega
  have hcore := Section63b.prop61_core m hm0 hmod hn64 hr2 h31
  have hsigpos : (0 : ℝ) < (Section51.sig m : ℝ) := by
    have h1 := Section51.sig_ge hm0
    have h2 : 0 < Section51.sig m := lt_of_lt_of_le hm0 h1
    exact_mod_cast h2
  have h24 : (0 : ℝ) < 24 * (Section51.sig m : ℝ) := by positivity
  have hsum : ∑ p ∈ Section5.PT (2 * m), (Section42.bp p (2 * m) : ℝ)
      < 16 * (Section51.sig m : ℝ) := by
    have h := hcore
    rw [one_div, inv_mul_lt_iff₀ h24] at h
    linarith
  have hnat : ∑ p ∈ Section5.PT (2 * m), Section42.bp p (2 * m)
      < (Sufficiency.Rmix (2 * m)).card := by
    have h1 : ((∑ p ∈ Section5.PT (2 * m), Section42.bp p (2 * m) : ℕ) : ℝ)
        < 16 * (Section51.sig m : ℝ) := by
      push_cast
      exact hsum
    have h2 : (16 : ℝ) * (Section51.sig m : ℝ) ≤ ((Sufficiency.Rmix (2 * m)).card : ℝ) := by
      exact_mod_cast hJ
    have h3 := lt_of_lt_of_le h1 h2
    exact_mod_cast h3
  apply Sufficiency.sufficiency (2 * m)
  rw [Finset.sum_congr rfl (fun p _ => bp_eq p (2 * m))] at hnat
  exact hnat

end Section64

#print axioms Section64.euler_conditional
#print axioms Section64.hJ_of_jacobi

/-! ### Euler1747.lean merged verbatim (minus its import). Uses native_decide in allOk_true, so its axiom list includes Lean.ofReduceBool. -/
/-
  Euler1747.lean   (draft written 2026-11-16 by Claude; UNTESTED: no Lean toolchain was available
  when this was written. Expect small repairs against your Mathlib version; fix against what
  the compiler actually says.)

  Source: Howe, Huffman, Kohlmeyer, Kruer, "Euler's 1747 conjecture on sums of integers with
  restricted prime factors", hexagon:2611.00370v1 (credits OpenAI Codex).  This file is NOT their
  formalization; it is an independent attempt at part of it.

  WHAT THIS FILE PROVES (if it compiles):
    1. EulerGood is closed under multiplication, and EulerGood a -> a % 4 = 1.
    2. FINITE PART (the paper's Proposition 7.2): every n with n % 4 = 2 and n < 64^4 is a sum of
       two EulerGood numbers with the smaller summand at most 313.  Proved by an exhaustive
       computation checked with `native_decide`, which trusts the Lean compiler (Lean.ofReduceBool),
       not only the kernel.
    3. A CONDITIONAL theorem: Euler's conjecture follows from `AnalyticRange`.

  WHAT THIS FILE DOES NOT PROVE:
    `AnalyticRange` is the statement of the paper's Proposition 6.1 (n = 2m >= 64^4, m odd, all prime
    factors of m are 3 mod 4).  It is a HYPOTHESIS here, not a theorem.  Proving it needs the
    Ramanujan-Petersson bound through Jacquet-Langlands and the paper's sections 2-5, which are not
    in Mathlib and which I have not audited.  So `euler_1747_of_analytic_range` is NOT the full
    Euler conjecture; it is the reduction of it to Proposition 6.1.

  Run:  put this file in a project that depends on Mathlib (for example inside your geometry repo)
        and run `lake env lean Euler1747.lean`.  The `native_decide` step factors about 4 million
        numbers; expect minutes, not seconds.
-/

namespace Euler1747

/-- The set A of the paper: positive integers all of whose prime factors are 1 mod 4 (1 allowed). -/
def EulerGood (a : ℕ) : Prop :=
  0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p % 4 = 1

/-- Computable test for `EulerGood`. -/
def goodB (a : ℕ) : Bool :=
  decide (0 < a) && a.primeFactorsList.all (fun p => p % 4 == 1)

theorem goodB_iff (a : ℕ) : goodB a = true ↔ EulerGood a := by
  unfold goodB EulerGood
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨ha, hall⟩ := h
    refine ⟨ha, fun p hp hpd => hall p ?_⟩
    exact Nat.mem_primeFactorsList'.2 ⟨hp, hpd, ha.ne'⟩
  · rintro ⟨ha, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
    refine ⟨ha, fun p hp => ?_⟩
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactorsList'.1 hp
    exact h p hpp hpd

/-! ### Adjacent facts used by the paper -/

theorem good_mul {a b : ℕ} (ha : EulerGood a) (hb : EulerGood b) : EulerGood (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, fun p hp hpd => ?_⟩
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · exact ha.2 p hp h
  · exact hb.2 p hp h

theorem good_of_mul_left {a b : ℕ} (h : EulerGood (a * b)) : EulerGood a := by
  have hpos : 0 < a := Nat.pos_of_ne_zero (fun h0 => by simp [h0, EulerGood] at h)
  exact ⟨hpos, fun p hp hpd => h.2 p hp (Dvd.dvd.mul_right hpd b)⟩

theorem good_of_mul_right {a b : ℕ} (h : EulerGood (a * b)) : EulerGood b := by
  rw [mul_comm] at h
  exact good_of_mul_left h

/-- Elements of A are 1 mod 4 (the parity fact behind the paper's Lemma 7.1). -/
theorem good_mod_four (a : ℕ) (h : EulerGood a) : a % 4 = 1 := by
  induction a using Nat.recOnMul with
  | zero => exact absurd h.1 (lt_irrefl 0)
  | one => rfl
  | prime p hp => exact h.2 p hp (dvd_refl p)
  | mul a b iha ihb =>
    have ha := iha (good_of_mul_left h)
    have hb := ihb (good_of_mul_right h)
    rw [Nat.mul_mod, ha, hb]

/-! ### The finite part (Proposition 7.2) -/

/-- Possible smaller summands: the numbers 4i+1 with i <= 78 that are in A.  The paper lists 43 of them,
    ending at 313. -/
def cands : List ℕ := ((List.range 79).map (fun i => 4 * i + 1)).filter goodB

/- Sanity checks against the paper's list J (run with `lake env lean`; these are cheap). -/
#eval cands.length          -- the paper says 43
#eval cands.getLast?        -- the paper says 313

def checkOne (n : ℕ) : Bool :=
  cands.any (fun a => decide (a < n) && goodB (n - a))

/-- n = 4k+2 for every k < 2^22 = 4194304, i.e. every n = 2 mod 4 below 64^4 = 16777216. -/
def allOk : Bool := (List.range 4194304).all (fun k => checkOne (4 * k + 2))

/-- The computation. TRUSTS THE COMPILER via native_decide. -/
theorem allOk_true : allOk = true := by native_decide

theorem euler_finite (n : ℕ) (hn : n % 4 = 2) (hlt : n < 64 ^ 4) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n ∧ min a b ≤ 313 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  have h64 : (64 : ℕ) ^ 4 = 16777216 := by norm_num
  rw [h64] at hlt
  have hk : k < 4194304 := by omega
  have h := allOk_true
  unfold allOk at h
  have h2 := (List.all_eq_true.1 h) k (List.mem_range.2 hk)
  unfold checkOne at h2
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨a, ha, hlt', hb⟩ := h2
  obtain ⟨hmap, hga⟩ := List.mem_filter.1 ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hmap
  have hi' := List.mem_range.1 hi
  refine ⟨4 * i + 1, 4 * k + 2 - (4 * i + 1), (goodB_iff _).1 hga, (goodB_iff _).1 hb,
    by omega, ?_⟩
  exact le_trans (min_le_left _ _) (by omega)

/-! ### Conditional reduction of the full conjecture to Proposition 6.1 -/

/-- Statement of the paper's Proposition 6.1.  A HYPOTHESIS in this file, not a theorem. -/
def AnalyticRange : Prop :=
  ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = 2 * m

/-- Euler's 1747 conjecture, CONDITIONAL on `AnalyticRange` (Proposition 6.1 of the paper).
    This reproduces the paper's Lemma 2.1 and the finite-range case by strong induction. -/
theorem euler_1747_of_analytic_range (H : AnalyticRange) (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n := by
  obtain ⟨m, rfl, hm⟩ : ∃ m, n = 2 * m ∧ m % 2 = 1 := ⟨n / 2, by omega, by omega⟩
  clear hn
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hex : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 1
    · obtain ⟨p, hp, hpd, hp1⟩ := hex
      obtain ⟨m', rfl⟩ := hpd
      have hm' : m' % 2 = 1 :=
        Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hm)).2
      have hp2 := hp.two_le
      have hm'pos : 0 < m' := by omega
      have hlt : m' < p * m' := by nlinarith
      obtain ⟨a, b, ha, hb, hab⟩ := ih m' hlt hm'
      have hpg : EulerGood p :=
        ⟨hp.pos, fun q hq hqd => by rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 hqd]; exact hp1⟩
      exact ⟨p * a, p * b, good_mul hpg ha, good_mul hpg hb, by rw [← mul_add, hab]; ring⟩
    · have h3 : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3 := by
        intro p hp hpd
        rcases hp.eq_two_or_odd with h2 | h2
        · subst h2; omega
        · have : p % 4 ≠ 1 := fun h1 => hex ⟨p, hp, hpd, h1⟩
          omega
      by_cases hbig : 64 ^ 4 ≤ 2 * m
      · exact H m hm h3 hbig
      · obtain ⟨a, b, ha, hb, hab, -⟩ := euler_finite (2 * m) (by omega) (not_le.1 hbig)
        exact ⟨a, b, ha, hb, hab⟩

end Euler1747

#print axioms Euler1747.euler_finite
#print axioms Euler1747.euler_1747_of_analytic_range

/-! ### Section65: final conditional theorem (UNTESTED, not compiled anywhere)

PROVES (if it compiles): Euler's conjecture for every n = 2 mod 4, CONDITIONAL on three universal statements:
  Hr2  (two-square count, for each qualifying m),
  H31  (Prop 3.1 for each qualifying m: needs Lemma 3.2, OPEN),
  HJac (Jacobi: |R(2m)| = 24 sigma(m) for odd m).
Hr2 and HJac are classical true statements not yet in Mathlib; H31 is the paper's deep input.
The finite range n < 64^4 uses native_decide (trusts the compiler, not only the kernel). -/

namespace Section65
open Euler1747

def Hr2 : Prop := ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
  ∀ u : ℤ, 1 ≤ u → u ≤ ((2 * m : ℕ) : ℤ) →
    (Section42.R2 (2 * m) u).card ≤ 4 * Section62.Mn (2 * m)

def H31 : Prop := ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
  ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ Section63b.Pn (2 * m) →
    (Section42.bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
      ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
        + (if 3 < p then (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ))
           else 0)

def HJac : Prop := ∀ m : ℕ, m % 2 = 1 → (FourSq.R (2 * m)).card = 24 * Section51.sig m

theorem analytic_range_of (hr2 : Hr2) (h31 : H31) (hjac : HJac) : AnalyticRange := by
  intro m hm hmod hn64
  exact Section64.euler_conditional m hm hmod hn64 (hr2 m hm hmod hn64)
    (h31 m hm hmod hn64) (Section64.hJ_of_jacobi m hm (hjac m hm))

theorem euler_1747_conditional (hr2 : Hr2) (h31 : H31) (hjac : HJac) (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n :=
  euler_1747_of_analytic_range (analytic_range_of hr2 h31 hjac) n hn

end Section65

#print axioms Section65.euler_1747_conditional


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

namespace Section65

/-- `Hr2` discharged: the two-square count (Stage66a-e) proves it for every box size. -/
theorem hr2 : Hr2 := by
  intro m _ _ _ u hu hun
  exact Section66e.hr2_all (2 * m) u hu hun

/-- Euler's 1747 conjecture for n = 2 mod 4, conditional on H31 and HJac only. -/
theorem euler_1747_of_H31_HJac (h31 : H31) (hjac : HJac) (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n :=
  euler_1747_conditional hr2 h31 hjac n hn

end Section65

#print axioms Section65.hr2
#print axioms Section65.euler_1747_of_H31_HJac
