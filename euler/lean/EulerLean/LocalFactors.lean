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
