import Mathlib

/-!
# DivCert_isolated.lean   (ISOLATED; UNTESTED: not compiled anywhere when written)

Needs only `import Mathlib` (pinned: Lean v4.32.0, Mathlib 81a5d257).  Touches NO production file.
Section 0 copies, verbatim, the small part of `Stage63b.lean` (`Section51`) that `Fq` needs, in the
separate namespace `DivCert`, so that the statements below are about definitions IDENTICAL to production's.
Nothing here is an axiom or a stub.  Run:   lake env lean EulerLean/ED/DivCert_isolated.lean

PROVES (if it compiles):
  A.  Fq m ≤ 11538016561723953609/335544320000000000   for m>0 with every prime factor ≡ 3 mod 4
      (exact local factors F5 p e;  decrease for e ≥ 4;  F5 ≤ 1 for p ≥ 32; finite checks for 3,7,11,19,23,31).
  B.  E := τ(m)√m/(3σ(m)) ≤ (5/6)/u^6   whenever u^20 = 2m and Fq m ≤ F0   (tenth-power route,
      (E u^6)^10 = 8 Fq(m)^2 / 3^10 and 8 F0^2 ≤ (5/2)^10).
  C.  numeric_core with E-coefficient 5/6 and error multiplier K = 4/3 (and K = 1); endpoint total
      2969397442715740783871/4483104393898701523350 < 2/3.
DOES NOT PROVE: any spectral statement, HPrime, HWeak, or anything about the prime-3 count.
Integration into Stage63b / Stage83cut is NOT done and not authorised.
-/

namespace DivCert

/-! ## 0. verbatim copies from Stage63b.lean (Section51) -/

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

/-! ## 1. exact local factor -/

/-- sigma(p^e) -/
def ssum (p e : ℕ) : ℕ := ∑ k ∈ Finset.range (e + 1), p ^ k

/-- the fifth power of the local factor, exact -/
def F5 (p e : ℕ) : ℚ := ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 / ((ssum p e : ℕ) : ℚ) ^ 5

lemma Fq_pp_eq' {p : ℕ} (hp : p.Prime) (e : ℕ) : Fq (p ^ e) = F5 p e := by
  rw [Fq_pp_eq hp e, sig_pp hp e]
  <;> simp only [F5, ssum]

lemma ssum_ge_pow (p e : ℕ) : p ^ e ≤ ssum p e := by
  unfold ssum
  exact Finset.single_le_sum (f := fun k : ℕ => p ^ k) (fun k _ => Nat.zero_le _)
    (Finset.self_mem_range_succ e)

lemma ssum_succ_ge (p : ℕ) : ∀ e : ℕ, p * ssum p e ≤ ssum p (e + 1) := by
  intro e
  induction e with
  | zero => simp [ssum, Finset.sum_range_succ] <;> omega
  | succ n ih =>
    have h1 : ssum p (n + 1) = ssum p n + p ^ (n + 1) := by
      unfold ssum; rw [Finset.sum_range_succ]
    have h2 : ssum p (n + 1 + 1) = ssum p (n + 1) + p ^ (n + 1 + 1) := by
      unfold ssum; rw [Finset.sum_range_succ]
    have h3 : p * ssum p (n + 1) = p * ssum p n + p ^ (n + 1 + 1) := by
      rw [h1]; ring
    rw [h2, h3]
    linarith [ih]

/-- the step: F5 does not increase from e to e+1 once e ≥ 4 (p ≥ 3) -/
lemma F5_succ_le {p e : ℕ} (hp : 3 ≤ p) (he : 4 ≤ e) : F5 p (e + 1) ≤ F5 p e := by
  have hpq : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have heq : (4 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  have hge : p ^ e ≤ ssum p e := ssum_ge_pow p e
  have hSpos : (0 : ℚ) < ((ssum p e : ℕ) : ℚ) := by
    have h0 : 0 < ssum p e := lt_of_lt_of_le (pow_pos (by omega) e) hge
    exact_mod_cast h0
  have hS' : (p : ℚ) * ((ssum p e : ℕ) : ℚ) ≤ ((ssum p (e + 1) : ℕ) : ℚ) := by
    exact_mod_cast ssum_succ_ge p e
  have hS'pos : (0 : ℚ) < ((ssum p (e + 1) : ℕ) : ℚ) :=
    lt_of_lt_of_le (mul_pos hp0 hSpos) hS'
  have h5 : ((e : ℚ) + 1 + 1) ^ 5 ≤ ((e : ℚ) + 1) ^ 5 * (p : ℚ) := by
    have h1 : 5 * ((e : ℚ) + 1 + 1) ≤ 6 * ((e : ℚ) + 1) := by linarith
    have h2' := pow_le_pow_left₀ (by linarith : (0 : ℚ) ≤ 5 * ((e : ℚ) + 1 + 1)) h1 5
    have h2 : (3125 : ℚ) * ((e : ℚ) + 1 + 1) ^ 5 ≤ 7776 * ((e : ℚ) + 1) ^ 5 := by
      calc (3125 : ℚ) * ((e : ℚ) + 1 + 1) ^ 5 = (5 * ((e : ℚ) + 1 + 1)) ^ 5 := by ring
        _ ≤ (6 * ((e : ℚ) + 1)) ^ 5 := h2'
        _ = 7776 * ((e : ℚ) + 1) ^ 5 := by ring
    have h3 : (0 : ℚ) ≤ ((e : ℚ) + 1) ^ 5 := by positivity
    have h4 : ((e : ℚ) + 1) ^ 5 * 3 ≤ ((e : ℚ) + 1) ^ 5 * (p : ℚ) :=
      mul_le_mul_of_nonneg_left hpq h3
    linarith [h2, h3, h4]
  have e1 : ((p : ℚ) ^ (e + 1)) ^ 4 = ((p : ℚ) ^ e) ^ 4 * (p : ℚ) ^ 4 := by ring
  have hS5 : (p : ℚ) ^ 5 * ((ssum p e : ℕ) : ℚ) ^ 5 ≤ ((ssum p (e + 1) : ℕ) : ℚ) ^ 5 := by
    have := pow_le_pow_left₀ (mul_pos hp0 hSpos).le hS' 5
    rwa [mul_pow] at this
  unfold F5
  rw [div_le_div_iff₀ (pow_pos hS'pos 5) (pow_pos hSpos 5)]
  push_cast
  rw [e1]
  have hnn : 0 ≤ ((p : ℚ) ^ e) ^ 4 * (p : ℚ) ^ 4 * ((ssum p e : ℕ) : ℚ) ^ 5 := by positivity
  calc ((e : ℚ) + 1 + 1) ^ 5 * (((p : ℚ) ^ e) ^ 4 * (p : ℚ) ^ 4) * ((ssum p e : ℕ) : ℚ) ^ 5
      = ((e : ℚ) + 1 + 1) ^ 5 * (((p : ℚ) ^ e) ^ 4 * (p : ℚ) ^ 4 * ((ssum p e : ℕ) : ℚ) ^ 5) := by
        ring
    _ ≤ ((e : ℚ) + 1) ^ 5 * (p : ℚ) * (((p : ℚ) ^ e) ^ 4 * (p : ℚ) ^ 4 * ((ssum p e : ℕ) : ℚ) ^ 5) :=
        mul_le_mul_of_nonneg_right h5 hnn
    _ = ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 * ((p : ℚ) ^ 5 * ((ssum p e : ℕ) : ℚ) ^ 5) := by
        ring
    _ ≤ ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 * ((ssum p (e + 1) : ℕ) : ℚ) ^ 5 :=
        mul_le_mul_of_nonneg_left hS5 (by positivity)

/-- if the bound B holds for e = 0..4 it holds for every e (p ≥ 3) -/
lemma F5_le_all {p : ℕ} (hp : 3 ≤ p) (B : ℚ) (h4 : ∀ e : ℕ, e ≤ 4 → F5 p e ≤ B) :
    ∀ e : ℕ, F5 p e ≤ B := by
  have hge : ∀ e : ℕ, 4 ≤ e → F5 p e ≤ B := by
    intro e he
    induction e, he using Nat.le_induction with
    | base => exact h4 4 le_rfl
    | succ n hn ih => exact le_trans (F5_succ_le hp hn) ih
  intro e
  by_cases he : e ≤ 4
  · exact h4 e he
  · exact hge e (by omega)

lemma succ_le_two_pow : ∀ e : ℕ, e + 1 ≤ 2 ^ e := by
  intro e
  induction e with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- p ≥ 32 : F5 ≤ 1 -/
lemma F5_le_one_of_ge32 {p : ℕ} (hp : 32 ≤ p) (e : ℕ) : F5 p e ≤ 1 := by
  have hge : p ^ e ≤ ssum p e := ssum_ge_pow p e
  have hpe : (e + 1) ^ 5 ≤ p ^ e := by
    calc (e + 1) ^ 5 ≤ (2 ^ e) ^ 5 := Nat.pow_le_pow_left (succ_le_two_pow e) 5
      _ = 32 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ p ^ e := Nat.pow_le_pow_left hp e
  have h1 : ((e : ℚ) + 1) ^ 5 ≤ (p : ℚ) ^ e := by exact_mod_cast hpe
  have h2 : (p : ℚ) ^ e ≤ ((ssum p e : ℕ) : ℚ) := by exact_mod_cast hge
  have hSpos : (0 : ℚ) < ((ssum p e : ℕ) : ℚ) := by
    have h0 : 0 < ssum p e := lt_of_lt_of_le (pow_pos (by omega) e) hge
    exact_mod_cast h0
  unfold F5
  rw [div_le_one (pow_pos hSpos 5)]
  calc ((e : ℚ) + 1) ^ 5 * ((p : ℚ) ^ e) ^ 4 ≤ (p : ℚ) ^ e * ((p : ℚ) ^ e) ^ 4 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((p : ℚ) ^ e) ^ 5 := by ring
    _ ≤ ((ssum p e : ℕ) : ℚ) ^ 5 := pow_le_pow_left₀ (by positivity) h2 5

/-! ## 2. the six exceptional primes -/

/-- exact maxima of F5 (1 at every other prime) -/
def betaX (p : ℕ) : ℚ :=
  if p = 3 then 531441 / 100000
  else if p = 7 then 2401 / 1024
  else if p = 11 then 14641 / 7776
  else if p = 19 then 130321 / 100000
  else if p = 23 then 279841 / 248832
  else 1

def S5 : Finset ℕ := {3, 7, 11, 19, 23}

lemma betaX_ge_one {q : ℕ} (hq : q ∈ S5) : 1 ≤ betaX q := by
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num [betaX]

lemma betaX_nonneg (q : ℕ) : 0 ≤ betaX q := by
  unfold betaX
  split_ifs <;> norm_num

lemma S5_prime {q : ℕ} (hq : q ∈ S5) : q.Prime := by
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma F5_p3 (e : ℕ) : F5 3 e ≤ 531441 / 100000 :=
  F5_le_all (p := 3) (by norm_num) _ (fun e he => by
    interval_cases e <;> norm_num [F5, ssum, Finset.sum_range_succ]) e

lemma F5_p7 (e : ℕ) : F5 7 e ≤ 2401 / 1024 :=
  F5_le_all (p := 7) (by norm_num) _ (fun e he => by
    interval_cases e <;> norm_num [F5, ssum, Finset.sum_range_succ]) e

lemma F5_p11 (e : ℕ) : F5 11 e ≤ 14641 / 7776 :=
  F5_le_all (p := 11) (by norm_num) _ (fun e he => by
    interval_cases e <;> norm_num [F5, ssum, Finset.sum_range_succ]) e

lemma F5_p19 (e : ℕ) : F5 19 e ≤ 130321 / 100000 :=
  F5_le_all (p := 19) (by norm_num) _ (fun e he => by
    interval_cases e <;> norm_num [F5, ssum, Finset.sum_range_succ]) e

lemma F5_p23 (e : ℕ) : F5 23 e ≤ 279841 / 248832 :=
  F5_le_all (p := 23) (by norm_num) _ (fun e he => by
    interval_cases e <;> norm_num [F5, ssum, Finset.sum_range_succ]) e

lemma F5_p31 (e : ℕ) : F5 31 e ≤ 1 :=
  F5_le_all (p := 31) (by norm_num) _ (fun e he => by
    interval_cases e <;> norm_num [F5, ssum, Finset.sum_range_succ]) e

/-- Fq at a prime power, p ≡ 3 mod 4: ≤ betaX p at the five primes, ≤ 1 otherwise (all e, including 0) -/
lemma Fq_pp_le_exact {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (e : ℕ) :
    Fq (p ^ e) ≤ if p ∈ S5 then betaX p else 1 := by
  rw [Fq_pp_eq' hp e]
  by_cases hpS : p ∈ S5
  · rw [if_pos hpS]
    simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hpS
    rcases hpS with rfl | rfl | rfl | rfl | rfl
    · simpa [betaX] using F5_p3 e
    · simpa [betaX] using F5_p7 e
    · simpa [betaX] using F5_p11 e
    · simpa [betaX] using F5_p19 e
    · simpa [betaX] using F5_p23 e
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
      · exact F5_p31 e
    · exact F5_le_one_of_ge32 (not_lt.1 h32) e

/-! ## 3. multiplicative bookkeeping (verbatim pattern of Stage63b, with betaX) -/

def Phi (m : ℕ) : ℚ := ∏ q ∈ S5, (if q ∣ m then betaX q else 1)

lemma Phi_nonneg (m : ℕ) : 0 ≤ Phi m := by
  unfold Phi
  apply Finset.prod_nonneg
  intro q _
  split_ifs
  · exact betaX_nonneg q
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
    Phi (p ^ n) = if p ∈ S5 then betaX p else 1 := by
  unfold Phi
  have hcong : ∀ q ∈ S5, (if q ∣ p ^ n then betaX q else 1) = if q = p then betaX q else 1 := by
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
    exact Fq_pp_le_exact hp h4 n
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

/-- A. the exact product bound -/
theorem Fq_le_F0 (m : ℕ) (hm : 0 < m) (hmod : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) :
    Fq m ≤ 11538016561723953609 / 335544320000000000 := by
  refine le_trans (Fq_le_Phi m hm hmod) ?_
  unfold Phi
  calc ∏ q ∈ S5, (if q ∣ m then betaX q else 1) ≤ ∏ q ∈ S5, betaX q := by
        apply Finset.prod_le_prod
        · intro q _
          split_ifs
          · exact betaX_nonneg q
          · norm_num
        · intro q hq
          split_ifs
          · exact le_refl _
          · exact betaX_ge_one hq
    _ = 11538016561723953609 / 335544320000000000 := by
        norm_num [S5, betaX, Finset.prod_insert]

lemma F0_lt_203 :
    (11538016561723953609 / 335544320000000000 : ℚ) < (203 / 100) ^ 5 := by norm_num

lemma F0_tenth :
    8 * (11538016561723953609 / 335544320000000000 : ℚ) ^ 2 < (5 / 2) ^ 10 := by norm_num

/-! ## B. the direct conversion to E -/

theorem E_le_five_sixths (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : 0 < u)
    (hu20 : u ^ 20 = 2 * (m : ℝ))
    (hF : Fq m ≤ 11538016561723953609 / 335544320000000000) :
    (tau m : ℝ) * Real.sqrt (m : ℝ) / (3 * (sig m : ℝ)) ≤ (5 / 6) / u ^ 6 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsig : (0 : ℝ) < (sig m : ℝ) := by
    have h := sig_ge hm
    have h0 : 0 < sig m := lt_of_lt_of_le hm h
    exact_mod_cast h0
  have hsigne : (sig m : ℝ) ≠ 0 := hsig.ne'
  have hq' : ((Fq m : ℚ) : ℝ) ≤ ((11538016561723953609 / 335544320000000000 : ℚ) : ℝ) :=
    Rat.cast_le.2 hF
  unfold Fq at hq'
  push_cast at hq'
  have hs0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (tau m : ℝ) * Real.sqrt (m : ℝ) / (3 * (sig m : ℝ)) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have e1 : E ^ 10 = (tau m : ℝ) ^ 10 * (Real.sqrt (m : ℝ) ^ 2) ^ 5
      / (3 ^ 10 * (sig m : ℝ) ^ 10) := by
    rw [hE]
    first | (field_simp; done) | (field_simp; ring)
  have key : (E * u ^ 6) ^ 10
      = 8 * ((tau m : ℝ) ^ 5 * (m : ℝ) ^ 4 / (sig m : ℝ) ^ 5) ^ 2 / 3 ^ 10 := by
    have e2 : (E * u ^ 6) ^ 10 = E ^ 10 * (u ^ 20) ^ 3 := by ring
    rw [e2, e1, hs2, hu20]
    first | (field_simp; done) | (field_simp; ring)
  have hFnn : 0 ≤ (tau m : ℝ) ^ 5 * (m : ℝ) ^ 4 / (sig m : ℝ) ^ 5 := by positivity
  have hsq := pow_le_pow_left₀ hFnn hq' 2
  have hnum : 8 * (11538016561723953609 / 335544320000000000 : ℝ) ^ 2 / 3 ^ 10
      ≤ (5 / 6 : ℝ) ^ 10 := by norm_num
  have hle10 : (E * u ^ 6) ^ 10 ≤ (5 / 6 : ℝ) ^ 10 := by
    rw [key]
    calc 8 * ((tau m : ℝ) ^ 5 * (m : ℝ) ^ 4 / (sig m : ℝ) ^ 5) ^ 2 / 3 ^ 10
        ≤ 8 * (11538016561723953609 / 335544320000000000 : ℝ) ^ 2 / 3 ^ 10 := by gcongr
      _ ≤ (5 / 6 : ℝ) ^ 10 := hnum
  have hbase : E * u ^ 6 ≤ 5 / 6 :=
    (pow_le_pow_iff_left₀ (mul_nonneg hE0 (pow_nonneg hu.le 6)) (by norm_num)
      (by norm_num : (10 : ℕ) ≠ 0)).1 hle10
  rw [le_div_iff₀ (pow_pos hu 6)]
  exact hbase

/-! ## C. the revised arithmetic budget -/

theorem numeric_core_E56_K43 (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 4 / 9) :
    21 / 50 + (4 / 3) * ((5 / 6) * (4 / 15 * w + w ^ 6))
      + (44 / 15) * (128 / (15 * 127) * w + 8192 / 16129 * w ^ 6 + 2 / 15 * w ^ 6 + w ^ 16)
    < 2 / 3 := by
  have h6 : w ^ 6 ≤ (4 / 9) ^ 6 := pow_le_pow_left₀ hw0.le hw 6
  have h16 : w ^ 16 ≤ (4 / 9) ^ 16 := pow_le_pow_left₀ hw0.le hw 16
  first
    | linarith
    | (norm_num at h6 h16 ⊢; linarith)
    | nlinarith [h6, h16, hw, hw0]

theorem numeric_core_E56_K1 (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 4 / 9) :
    21 / 50 + ((5 / 6) * (4 / 15 * w + w ^ 6))
      + (44 / 15) * (128 / (15 * 127) * w + 8192 / 16129 * w ^ 6 + 2 / 15 * w ^ 6 + w ^ 16)
    < 2 / 3 := by
  have h6 : w ^ 6 ≤ (4 / 9) ^ 6 := pow_le_pow_left₀ hw0.le hw 6
  have h16 : w ^ 16 ≤ (4 / 9) ^ 16 := pow_le_pow_left₀ hw0.le hw 16
  first
    | linarith
    | (norm_num at h6 h16 ⊢; linarith)
    | nlinarith [h6, h16, hw, hw0]

/-- the exact endpoint total at w = 4/9 and its strict comparison -/
theorem endpoint_K43 :
    (21 / 50 + (4 / 3) * ((5 / 6) * (4 / 15 * (4 / 9 : ℚ) + (4 / 9 : ℚ) ^ 6))
      + (44 / 15) * (128 / (15 * 127) * (4 / 9 : ℚ) + 8192 / 16129 * (4 / 9 : ℚ) ^ 6
          + 2 / 15 * (4 / 9 : ℚ) ^ 6 + (4 / 9 : ℚ) ^ 16))
      = 2969397442715740783871 / 4483104393898701523350 := by norm_num

theorem endpoint_K43_lt : (2969397442715740783871 / 4483104393898701523350 : ℚ) < 2 / 3 := by
  norm_num

end DivCert

#print axioms DivCert.Fq_le_F0
#print axioms DivCert.E_le_five_sixths
#print axioms DivCert.numeric_core_E56_K43
#print axioms DivCert.numeric_core_E56_K1
#print axioms DivCert.endpoint_K43
