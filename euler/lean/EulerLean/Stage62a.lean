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

#print axioms LocalFactors.max_p3
#print axioms LocalFactors.max_q29
#print axioms LocalFactors.large_prime

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
  exact Finset.filter_subset _ _

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
    have h := Nat.factorization_prod_pow_eq_self hu
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
  first
    | exact (pow_le_pow_iff_left₀ hX hY (by norm_num)).1 hle
    | exact (pow_le_pow_iff_left hX hY (by norm_num)).1 hle

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

#print axioms Section62.local_q
#print axioms Section62.ratio_subsets
#print axioms Section62.Mq_pow5
#print axioms Section62.Mn_le
