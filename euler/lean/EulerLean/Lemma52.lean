import Mathlib

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

#print axioms Section5.prime_count_bound
#print axioms Section5.prime_tail
#print axioms Section5.five_four
