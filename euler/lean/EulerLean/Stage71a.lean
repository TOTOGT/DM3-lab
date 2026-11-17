import Mathlib

/-! # Stage71a: the covering lemma behind Hurwitz Euclidean division (UNTESTED when written; no compiler run yet)

WHAT THIS FILE PROVES, if it compiles.  For every x in Q^4 there is a Hurwitz point q (all four coordinates
integers, or all four in Z + 1/2) with  sum (x_i - q_i)^2 < 1.

Hand derivation.  Round each coordinate: e_i = x_i - round(x_i), |e_i| <= 1/2, so e_i^2 <= 1/4 and the four
squares sum to at most 1.  If some |e_i| < 1/2, that term is < 1/4 and the sum is < 1: take q = (round x_i).
Otherwise every |e_i| = 1/2, so every x_i lies in Z + 1/2, x is itself a Hurwitz point, and q = x gives 0.

THIS IS THE ROUNDING STEP ONLY.  It is Step B of JACOBI_PLAN.md reduced to a statement about Q^4.  It does NOT
define the Hurwitz order as a subring of the quaternions, does NOT prove that the order is closed under
multiplication, and does NOT prove Euclidean division (that needs a - q b = (a b^-1 - q) b and multiplicativity of
the norm).  It does not discharge HJac. -/

open Finset

namespace Section71

/-- the Hurwitz lattice inside Q^4: all coordinates integers, or all in Z + 1/2 -/
def IsHur (q : Fin 4 → ℚ) : Prop :=
  (∀ i, ∃ z : ℤ, q i = z) ∨ (∀ i, ∃ z : ℤ, q i = z + 1 / 2)

theorem cover (x : Fin 4 → ℚ) : ∃ q : Fin 4 → ℚ, IsHur q ∧ ∑ i, (x i - q i) ^ 2 < 1 := by
  by_cases hall : ∀ i, |x i - round (x i)| = 1 / 2
  · refine ⟨x, Or.inr ?_, by simp⟩
    intro i
    have h := hall i
    rcases abs_eq (by norm_num : (0 : ℚ) ≤ 1 / 2) |>.1 h with h1 | h1
    · exact ⟨round (x i), by linarith⟩
    · exact ⟨round (x i) - 1, by push_cast; linarith⟩
  · push_neg at hall
    obtain ⟨i0, hi0⟩ := hall
    have hle : ∀ i, (x i - round (x i)) ^ 2 ≤ 1 / 4 := by
      intro i
      have := abs_le.1 (abs_sub_round (x i))
      nlinarith [this.1, this.2]
    have hlt : (x i0 - round (x i0)) ^ 2 < 1 / 4 := by
      have h1 := abs_sub_round (x i0)
      have h2 : |x i0 - round (x i0)| < 1 / 2 := lt_of_le_of_ne h1 hi0
      have := abs_lt.1 h2
      nlinarith [this.1, this.2]
    refine ⟨fun i => ((round (x i) : ℤ) : ℚ), Or.inl (fun i => ⟨round (x i), rfl⟩), ?_⟩
    calc ∑ i, (x i - ((round (x i) : ℤ) : ℚ)) ^ 2
        < ∑ _i : Fin 4, (1 / 4 : ℚ) :=
          Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, Finset.mem_univ _, hlt⟩
      _ = 1 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num

end Section71

#print axioms Section71.cover
