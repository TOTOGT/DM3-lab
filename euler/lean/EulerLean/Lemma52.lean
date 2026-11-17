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
It does NOT prove (5.3) or (5.4) (the tail sums); those need partial summation.
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

end Section5

#print axioms Section5.prime_count_bound
