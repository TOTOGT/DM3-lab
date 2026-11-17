import Mathlib

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
    · have hd : q ∣ p ^ n := h ▸ dvd_pow_self p (by omega)
      rw [if_pos hd, if_pos h]
    · have hd : ¬ q ∣ p ^ n := fun hd =>
        h ((Nat.prime_dvd_prime_iff_eq hqp hp).1 (hqp.dvd_of_dvd_pow hd))
      rw [if_neg hd, if_neg h]
  rw [Finset.prod_congr rfl hcong]
  rw [Finset.prod_ite_eq']

theorem Fq_le_Phi (m : ℕ) :
    0 < m → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → Fq m ≤ Phi m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | hp p n hp hn =>
    intro _ hmod
    have h4 := hmod p hp (dvd_pow_self p (by omega))
    rw [Phi_pp hp hn]
    exact Fq_pp_le hp h4 hn
  | h0 => intro h; omega
  | h1 =>
    intro _ _
    have : Fq 1 = 1 := by unfold Fq; rw [tau_one, sig_one]; norm_num
    rw [this, Phi_one]
  | h a b ha hb hab iha ihb =>
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
  unfold Fq at hq
  have hR : ((tau m : ℝ)) ^ 5 * (m : ℝ) ^ 4 / ((sig m : ℝ)) ^ 5
      ≤ (183143120027364343 / 2849934139195392 : ℝ) := by exact_mod_cast hq
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

#print axioms LocalFactors.max_p3
#print axioms Section51.Fq_le_Phi
#print axioms Section51.tau_sigma_pow5
#print axioms Section51.lemma51_first
