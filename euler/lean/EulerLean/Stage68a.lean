/-
  HurwitzStepA.lean   (draft written 2026-11-16 by Claude; first compile in GitHub Actions gave 2 omega errors from unreduced lambdas; patched, NOT re-run)

  Step A of EulerLean/JACOBI_PLAN.md.

  WHAT THIS FILE PROVES, if it compiles:
    For EVEN n, the set of "Hurwitz numerators" of norm n has the same cardinality as the set of
    integer 4-tuples with sum of squares n.   (Element of norm n = u/2 with  sum u_i^2 = 4n,
    all u_i even or all u_i odd.)   Reason: four odd squares sum to 4 mod 8, but 4n = 0 mod 8 for even n,
    so every such u is all-even, i.e. u = 2x with x in Z^4.

  WHAT THIS FILE DOES NOT PROVE:
    It does not define the Hurwitz ORDER as a ring, does not show it is Euclidean (Step B), and does
    not count it (Step C).  It does NOT prove  r4(2m) = 24*sigma(m);  it only removes the half-integer
    case for even n.  `hurwitzNum` is a set of integer numerator tuples, not quaternions.

  Run:  cd ~/Desktop/DM3-lab/euler/lean
        lake env lean EulerLean/HurwitzStepA.lean
-/
import Mathlib

namespace HurwitzA

/-- Integer 4-tuples with sum of squares `n`. -/
def lipschitz (n : ℕ) : Set (Fin 4 → ℤ) := {x | ∑ i, x i ^ 2 = (n : ℤ)}

/-- Numerators `u` of Hurwitz elements `u/2` of norm `n`: all even or all odd, `∑ u_i^2 = 4n`. -/
def hurwitzNum (n : ℕ) : Set (Fin 4 → ℤ) :=
  {u | ((∀ i, u i % 2 = 0) ∨ (∀ i, u i % 2 = 1)) ∧ ∑ i, u i ^ 2 = 4 * (n : ℤ)}

theorem odd_sq_mod_eight (x : ℤ) (h : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self k
  have h1 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [h1, ht]
  omega

/-- Four odd numerators cannot have sum of squares `4n` with `n` even. -/
theorem no_all_odd (n : ℤ) (hn : n % 2 = 0) (u : Fin 4 → ℤ) (hodd : ∀ i, u i % 2 = 1)
    (hs : ∑ i, u i ^ 2 = 4 * n) : False := by
  rw [Fin.sum_univ_four] at hs
  have h0 := odd_sq_mod_eight _ (hodd 0)
  have h1 := odd_sq_mod_eight _ (hodd 1)
  have h2 := odd_sq_mod_eight _ (hodd 2)
  have h3 := odd_sq_mod_eight _ (hodd 3)
  omega

theorem even_norm_all_even (n : ℤ) (hn : n % 2 = 0) (u : Fin 4 → ℤ)
    (hu : (∀ i, u i % 2 = 0) ∨ (∀ i, u i % 2 = 1)) (hs : ∑ i, u i ^ 2 = 4 * n) :
    ∀ i, u i % 2 = 0 := by
  rcases hu with h | h
  · exact h
  · exact (no_all_odd n hn u h hs).elim

theorem hurwitz_eq_image (n : ℕ) (hn : n % 2 = 0) :
    hurwitzNum n = (fun x : Fin 4 → ℤ => fun i => 2 * x i) '' lipschitz n := by
  have hnz : (n : ℤ) % 2 = 0 := by omega
  ext u
  constructor
  · rintro ⟨hu, hs⟩
    have he := even_norm_all_even (n : ℤ) hnz u hu hs
    have hx : ∀ i, u i = 2 * (u i / 2) := fun i => by have := he i; omega
    have hsum : ∑ i, u i ^ 2 = 4 * ∑ i, (u i / 2) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      calc u i ^ 2 = (2 * (u i / 2)) ^ 2 := by rw [← hx i]
        _ = 4 * (u i / 2) ^ 2 := by ring
    refine ⟨fun i => u i / 2, ?_, ?_⟩
    · show ∑ i, (u i / 2) ^ 2 = (n : ℤ)
      omega
    · funext i
      exact (hx i).symm
  · rintro ⟨x, hx, rfl⟩
    have hsum : ∑ i, (2 * x i) ^ 2 = 4 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hx' : ∑ i, x i ^ 2 = (n : ℤ) := hx
    refine ⟨Or.inl (fun i => ?_), ?_⟩
    · show 2 * x i % 2 = 0
      omega
    · show ∑ i, (2 * x i) ^ 2 = 4 * (n : ℤ)
      rw [hsum, hx']

/-- Step A: for even `n`, as many Hurwitz numerators of norm `n` as integer 4-tuples of norm `n`. -/
theorem hurwitz_ncard_eq_lipschitz (n : ℕ) (hn : n % 2 = 0) :
    (hurwitzNum n).ncard = (lipschitz n).ncard := by
  rw [hurwitz_eq_image n hn]
  refine Set.ncard_image_of_injective _ (fun x y h => ?_)
  funext i
  have : 2 * x i = 2 * y i := congrFun h i
  omega

end HurwitzA

#print axioms HurwitzA.hurwitz_ncard_eq_lipschitz


/-! ### Stage68a: the even-norm Hurwitz count equals `FourSq.R`  (UNTESTED, not compiled anywhere)

`FourSq.R` below is copied verbatim from FourSquaresMixed.lean (Stage65 contains it) so this file is standalone.
PROVES (if it compiles):
  * lipschitz_eq_R        : HurwitzA.lipschitz n = (FourSq.R n : Set _)   (the box bounds follow from the norm equation)
  * hurwitz_ncard_eq_R    : n even  =>  (HurwitzA.hurwitzNum n).ncard = (FourSq.R n).card
DOES NOT PROVE: Jacobi's count.  Nothing here says (hurwitzNum n).ncard = 24 * sigma_odd n; that is Steps B and C
of JACOBI_PLAN.md (Euclidean division and unique factorization in the Hurwitz order), not started. -/

namespace FourSq

/-- Signed ordered representations of `n` as a sum of four squares, as a finite set. -/
noncomputable def R (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => ∑ i, x i ^ 2 = (n : ℤ))

end FourSq

namespace Section68

lemma le_sq'' (b : ℤ) : b ≤ b ^ 2 := by
  rcases le_or_gt b 0 with h | h
  · nlinarith [sq_nonneg b]
  · nlinarith [mul_nonneg h.le (by linarith : (0 : ℤ) ≤ b - 1)]

theorem lipschitz_eq_R (n : ℕ) : HurwitzA.lipschitz n = ↑(FourSq.R n) := by
  ext x
  simp only [FourSq.R, HurwitzA.lipschitz, Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [h] at hle
    have h1 : x i ≤ x i ^ 2 := le_sq'' (x i)
    have h2 : -x i ≤ x i ^ 2 := by
      have := le_sq'' (-x i)
      rwa [neg_sq] at this
    constructor <;> linarith
  · rintro ⟨_, h⟩
    exact h

theorem hurwitz_ncard_eq_R (n : ℕ) (hn : n % 2 = 0) :
    (HurwitzA.hurwitzNum n).ncard = (FourSq.R n).card := by
  rw [HurwitzA.hurwitz_ncard_eq_lipschitz n hn, lipschitz_eq_R, Set.ncard_coe_finset]

end Section68

#print axioms Section68.lipschitz_eq_R
#print axioms Section68.hurwitz_ncard_eq_R
