import Mathlib

/-! # Stage69a: the case p | m of H31  (UNTESTED when written; no compiler run yet)

WHAT THIS FILE PROVES, if it compiles.  For a prime p = 3 mod 4 dividing an odd m, with the hypothesis
`hmix` (|Rmix(2m')| = 16 sigma(m') for every odd m', which is Jacobi's count plus equation (2.2) and is
NOT proved here), the paper's bound
    b_p(2m) / (24 sigma(m)) <= 2/(p(p-1)) + (the same extra term as in H31, which is >= 0)
holds.  Route, by hand: if p divides one pair of coordinates of x in Rmix(2m) then p divides the other
pair too (-1 is a non-residue mod p, p | 2m), so b_p(2m) counts exactly the x with p | all four
coordinates; these are p times the elements of Rmix(2m / p^2) when p^2 | m, and there are none otherwise.
Then 16 sigma(m/p^2) * p (p-1) <= 16 sigma(m) <= 48 sigma(m) because sigma(m) >= p^2 sigma(m/p^2).
DOES NOT PROVE: the case p not dividing m (p = 3 and p > 3), which needs the Hurwitz-order machinery;
the hypothesis hmix.  The restated block below (Section51.tau, sig; Sufficiency.dvd_of_sq_add, Rmix,
Eset, bp) is copied from Stage67 so that this file compiles alone. -/

open Finset

namespace Section51
def tau (m : ℕ) : ℕ := ArithmeticFunction.sigma 0 m
def sig (m : ℕ) : ℕ := ArithmeticFunction.sigma 1 m
end Section51

namespace Sufficiency

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

end Sufficiency

namespace Section69
open Sufficiency

lemma sq_box {k : ℕ} {y : ℤ} (h : y ^ 2 ≤ (k : ℤ)) : -(k : ℤ) ≤ y ∧ y ≤ (k : ℤ) := by
  have hy : |y| ≤ y ^ 2 := by
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
      rcases eq_or_lt_of_le h0 with h1 | h1
      · rw [← h1]; norm_num
      · nlinarith
    · rw [abs_of_neg h0]; nlinarith
  have := abs_le.1 (le_trans hy h)
  exact this

lemma mem_Rmix {n : ℕ} {x : Fin 4 → ℤ} :
    x ∈ Rmix n ↔ (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1 ∧
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ) := by
  unfold Rmix
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro h; exact h.2
  · intro h
    refine ⟨?_, h⟩
    have hall : ∀ j : Fin 4, x j ^ 2 ≤ (n : ℤ) := by
      intro j
      fin_cases j <;> (try simp) <;>
        linarith [h.2.2, sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    intro i
    exact Finset.mem_Icc.2 (sq_box (hall i))

/-- if p = 3 mod 4 divides n, p divides one coordinate pair of x in Rmix n, then it divides all four -/
lemma all_dvd {p n : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpn : p ∣ n)
    {x : Fin 4 → ℤ} (hx : x ∈ Rmix n)
    (h : ((p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1) ∨ ((p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3)) :
    (p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1 ∧ (p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3 := by
  have hsum := ((mem_Rmix).1 hx).2.2
  have hpn' : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.2 hpn
  have hsq : ∀ y : ℤ, (p : ℤ) ∣ y → (p : ℤ) ∣ y ^ 2 := fun y hy => dvd_pow hy two_ne_zero
  rcases h with ⟨h0, h1⟩ | ⟨h2, h3'⟩
  · have hd : (p : ℤ) ∣ x 2 ^ 2 + x 3 ^ 2 := by
      have e : x 2 ^ 2 + x 3 ^ 2 = (n : ℤ) - (x 0 ^ 2 + x 1 ^ 2) := by linarith
      rw [e]; exact dvd_sub hpn' (dvd_add (hsq _ h0) (hsq _ h1))
    obtain ⟨h2, h3'⟩ := dvd_of_sq_add hp h3 _ _ hd
    exact ⟨h0, h1, h2, h3'⟩
  · have hd : (p : ℤ) ∣ x 0 ^ 2 + x 1 ^ 2 := by
      have e : x 0 ^ 2 + x 1 ^ 2 = (n : ℤ) - (x 2 ^ 2 + x 3 ^ 2) := by linarith
      rw [e]; exact dvd_sub hpn' (dvd_add (hsq _ h2) (hsq _ h3'))
    obtain ⟨h0, h1⟩ := dvd_of_sq_add hp h3 _ _ hd
    exact ⟨h0, h1, h2, h3'⟩

/-- Eset p n = elements of Rmix n all of whose coordinates are divisible by p (when p | n) -/
lemma mem_Eset {p n : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpn : p ∣ n) {x : Fin 4 → ℤ} :
    x ∈ Eset p n ↔ x ∈ Rmix n ∧ ((p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1 ∧ (p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3) := by
  unfold Eset
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hx, h⟩; exact ⟨hx, all_dvd hp h3 hpn hx h⟩
  · rintro ⟨hx, h0, h1, h2, h3'⟩; exact ⟨hx, Or.inl ⟨h0, h1⟩⟩

/-- if p divides every coordinate and the squares add to n, then p^2 divides n -/
lemma sq_dvd {p n : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ Rmix n)
    (h : (p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1 ∧ (p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3) : p ^ 2 ∣ n := by
  have hsum := ((mem_Rmix).1 hx).2.2
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := h
  have : (n : ℤ) = (p : ℤ) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    rw [← hsum, ha, hb, hc, hd]; ring
  have h2 : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, by push_cast; exact this⟩
  exact Int.natCast_dvd_natCast.1 h2

/-- b_p(n) = 0 unless p^2 | n -/
lemma bp_zero {p n : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpn : p ∣ n) (hn : ¬ p ^ 2 ∣ n) :
    bp p n = 0 := by
  unfold bp
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_Eset hp h3 hpn] at hx
  exact hn (sq_dvd hx.1 hx.2)

/-- when p^2 | n (p odd), Eset p n is the image of Rmix (n / p^2) under y -> p * y -/
lemma Eset_eq_image {p n : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpn : p ^ 2 ∣ n) :
    Eset p n = (Rmix (n / p ^ 2)).image (fun y i => (p : ℤ) * y i) := by
  have hp1 : p ∣ n := dvd_trans (dvd_pow_self p two_ne_zero) hpn
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hpodd : Odd (p : ℤ) := by
    rw [Int.odd_iff]; omega
  obtain ⟨k, hk⟩ := hpn
  have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hkk : n / p ^ 2 = k := by rw [hk]; exact Nat.mul_div_cancel_left k hpos
  rw [hkk]
  ext x
  rw [Finset.mem_image, mem_Eset hp h3 hp1]
  constructor
  · rintro ⟨hx, h0, h1, h2, h3'⟩
    obtain ⟨a, ha⟩ := h0; obtain ⟨b, hb⟩ := h1; obtain ⟨c, hc⟩ := h2; obtain ⟨d, hd⟩ := h3'
    refine ⟨![a, b, c, d], ?_, ?_⟩
    · have hm := (mem_Rmix).1 hx
      rw [mem_Rmix]
      refine ⟨?_, ?_, ?_⟩
      · have h01 : x 0 + x 1 = (p : ℤ) * (a + b) := by rw [ha, hb]; ring
        have hodd : Odd (x 0 + x 1) := Int.odd_iff.2 hm.1
        rw [h01] at hodd
        have := (Int.odd_mul.1 hodd).2
        simpa using Int.odd_iff.1 this
      · have h23 : x 2 + x 3 = (p : ℤ) * (c + d) := by rw [hc, hd]; ring
        have hodd : Odd (x 2 + x 3) := Int.odd_iff.2 hm.2.1
        rw [h23] at hodd
        have := (Int.odd_mul.1 hodd).2
        simpa using Int.odd_iff.1 this
      · have hs := hm.2.2
        have e : (p : ℤ) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = (p : ℤ) ^ 2 * (k : ℤ) := by
          have : (n : ℤ) = (p : ℤ) ^ 2 * (k : ℤ) := by rw [hk]; push_cast; ring
          rw [← this, ← hs, ha, hb, hc, hd]; ring
        have hp2 : (p : ℤ) ^ 2 ≠ 0 := by positivity
        have := mul_left_cancel₀ hp2 e
        simpa using this
    · funext i
      fin_cases i <;> simp [ha, hb, hc, hd]
  · rintro ⟨y, hy, rfl⟩
    have hm := (mem_Rmix).1 hy
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_Rmix]
      refine ⟨?_, ?_, ?_⟩
      · have : (p : ℤ) * y 0 + (p : ℤ) * y 1 = (p : ℤ) * (y 0 + y 1) := by ring
        show ((p : ℤ) * y 0 + (p : ℤ) * y 1) % 2 = 1
        rw [this]
        have hodd : Odd (y 0 + y 1) := Int.odd_iff.2 hm.1
        exact Int.odd_iff.1 (Odd.mul hpodd hodd)
      · have : (p : ℤ) * y 2 + (p : ℤ) * y 3 = (p : ℤ) * (y 2 + y 3) := by ring
        show ((p : ℤ) * y 2 + (p : ℤ) * y 3) % 2 = 1
        rw [this]
        have hodd : Odd (y 2 + y 3) := Int.odd_iff.2 hm.2.1
        exact Int.odd_iff.1 (Odd.mul hpodd hodd)
      · show ((p : ℤ) * y 0) ^ 2 + ((p : ℤ) * y 1) ^ 2 + ((p : ℤ) * y 2) ^ 2 + ((p : ℤ) * y 3) ^ 2 = (n : ℤ)
        have e : ((p : ℤ) * y 0) ^ 2 + ((p : ℤ) * y 1) ^ 2 + ((p : ℤ) * y 2) ^ 2 + ((p : ℤ) * y 3) ^ 2
            = (p : ℤ) ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) := by ring
        rw [e, hm.2.2, hk]; push_cast; ring
    · exact Dvd.intro _ rfl
    · exact Dvd.intro _ rfl
    · exact Dvd.intro _ rfl
    · exact Dvd.intro _ rfl

lemma sig_ge_sq {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    p ^ 2 * Section51.sig m ≤ Section51.sig (p ^ 2 * m) := by
  unfold Section51.sig
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply, Finset.mul_sum]
  have hinj : Function.Injective (fun d : ℕ => p ^ 2 * d) := by
    intro a b hab; exact Nat.eq_of_mul_eq_mul_left (pow_pos hp 2) hab
  rw [← Finset.sum_image (f := fun e : ℕ => e) (g := fun d : ℕ => p ^ 2 * d) (s := m.divisors)
      (fun a _ b _ hab => hinj hab)]
  apply Finset.sum_le_sum_of_subset
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨d, hd, rfl⟩ := he
  rw [Nat.mem_divisors] at hd ⊢
  exact ⟨Nat.mul_dvd_mul_left _ hd.1, by positivity⟩

lemma bp_card {p n : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hpn : p ^ 2 ∣ n) :
    bp p n = (Rmix (n / p ^ 2)).card := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold bp
  rw [Eset_eq_image hp h3 hpn]
  apply Finset.card_image_of_injective
  intro y z h
  funext i
  have := congrFun h i
  exact mul_left_cancel₀ hp0 this

/-- the case p | m of H31, given the Jacobi-plus-(2.2) count `hmix` as a hypothesis -/
theorem h31_dvd {m p : ℕ} (hm : m % 2 = 1) (hp : p.Prime) (h3 : p % 4 = 3) (hpm : p ∣ m)
    (hmix : ∀ m' : ℕ, m' % 2 = 1 → (Rmix (2 * m')).card = 16 * Section51.sig m') :
    (bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
      ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
        + (if 3 < p then (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ))
           else 0) := by
  have hm0 : 0 < m := by omega
  have hp3 : 3 ≤ p := by omega
  have hsig : m ≤ Section51.sig m := by
    unfold Section51.sig
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors.2 ⟨dvd_refl m, hm0.ne'⟩)
  have hsigR : (0 : ℝ) < (Section51.sig m : ℝ) := by exact_mod_cast lt_of_lt_of_le hm0 hsig
  have hextra : (0 : ℝ) ≤ (if 3 < p then (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ))
      else 0) := by
    split_ifs
    · positivity
    · exact le_refl _
  have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hpp : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  have hmain : 0 < 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
  have hpm2 : p ∣ 2 * m := Dvd.dvd.mul_left hpm 2
  by_cases h2 : p ^ 2 ∣ 2 * m
  · have hcop : Nat.Coprime (p ^ 2) 2 :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
    have hpm' : p ^ 2 ∣ m := Nat.Coprime.dvd_of_dvd_mul_left hcop h2
    obtain ⟨m', hm'⟩ := hpm'
    have hm'0 : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · subst h; simp at hm'; omega
      · exact h
    have hodd' : m' % 2 = 1 := by
      have hodd : Odd m := Nat.odd_iff.2 hm
      rw [hm'] at hodd
      exact Nat.odd_iff.1 (Nat.odd_mul.1 hodd).2
    have hdiv : (2 * m) / p ^ 2 = 2 * m' := by
      rw [hm']
      have : 2 * (p ^ 2 * m') = p ^ 2 * (2 * m') := by ring
      rw [this]
      exact Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)
    have hbp : bp p (2 * m) = 16 * Section51.sig m' := by
      rw [bp_card hp h3 h2, hdiv]; exact hmix m' hodd'
    have hge := sig_ge_sq hp.pos hm'0
    rw [← hm'] at hge
    have hgeR : (p : ℝ) ^ 2 * (Section51.sig m' : ℝ) ≤ (Section51.sig m : ℝ) := by exact_mod_cast hge
    have hs' : (0 : ℝ) ≤ (Section51.sig m' : ℝ) := by positivity
    have key : ((bp p (2 * m) : ℕ) : ℝ) * ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * (24 * (Section51.sig m : ℝ)) := by
      rw [hbp]; push_cast
      nlinarith [hgeR, hs', hsigR, hp3R, mul_nonneg hs' (by linarith : (0 : ℝ) ≤ (p : ℝ))]
    have hfirst : (bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ)) ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [div_le_div_iff₀ (by positivity) hpp]
      exact key
    linarith [hfirst, hextra]
  · have h0 : ((bp p (2 * m) : ℕ) : ℝ) = 0 := by rw [bp_zero hp h3 hpm2 h2]; simp
    rw [h0, zero_div]
    linarith [hmain, hextra]

end Section69

#print axioms Section69.h31_dvd
#print axioms Section69.bp_card
#print axioms Section69.sig_ge_sq
#print axioms Section69.Eset_eq_image
