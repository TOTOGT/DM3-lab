import StageA4o

/-!
# EDc3.lean   (UNTESTED until compiled by CI)

Phase 8C.  An UNCONDITIONAL piece of the spectral obligation behind `EDcDefs.HPrime204Restricted`.

`HPrime204Restricted` asks for `‖T_l f‖ ≤ (51/25) √l ‖f‖` for primes `l ≡ 3 (mod 4)` on `f ⟂ {1, χ}` in `L²(Y_p)`,
uniformly in `p`.  Everything elementary about `T_l` (self-adjoint, eigenvalues on `1` and `χ`, multiplicativity, the
prime-power recursion) is already checked in `StageA4o`.  What is missing is the SIZE of the eigenvalues on the
complement of `{1, χ}`.  That size is a Ramanujan–Petersson statement:  via Jacquet–Langlands the eigenvalues are Hecke
eigenvalues `a_l` of weight-2 cusp forms (trivial character, level dividing `2p²`), and the needed input is
`|a_l| ≤ 2 √l` for primes `l ∤ 2p` (Eichler–Shimura + Weil/Deligne).  Mathlib has neither.  NOT PROVED HERE.

What IS proved here, with no hypothesis:

* `Tl_norm_le` :  `‖T_n f‖ ≤ σ(n) ‖f‖` for every `f` in `L²(Y_p)` and every admissible `n`.
* `Tl_prime_norm_le` :  for a prime `l`, `‖T_l f‖ ≤ (l+1) ‖f‖`.

Proof (Schur test): `T_n f(y)` is `(1/24)` times a sum over the `24 σ(n)` Hurwitz elements of norm `n`, so by
Cauchy–Schwarz `|T_n f(y)|² ≤ σ(n) · T_n(|f|²)(y)`; summing over `y` and using self-adjointness together with
`T_n 1 = σ(n) 1` gives `‖T_n f‖² ≤ σ(n)² ‖f‖²`.

What this does NOT do:  it does not prove `HPrime204Restricted` for any prime `l`.  The trivial bound `l + 1` already
exceeds `(51/25) √l` at `l = 3` (4 versus about 3.53).  Its value is that it makes the remaining gap exact:
from `l + 1` down to `(51/25) √l`, which is the Ramanujan–Petersson input above.  `HPrime204Restricted` stays OPEN.
-/

namespace EDc3
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

/-- Cauchy–Schwarz for a finite sum of complex numbers. -/
theorem sq_norm_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ s, a i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, a i‖ ≤ ∑ i ∈ s, ‖a i‖ := norm_sum_le s a
  have h2 : ‖∑ i ∈ s, a i‖ * ‖∑ i ∈ s, a i‖ ≤ (∑ i ∈ s, ‖a i‖) * (∑ i ∈ s, ‖a i‖) :=
    mul_self_le_mul_self (norm_nonneg _) h1
  have h3 : (∑ i ∈ s, ‖a i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖a i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  nlinarith [h2, h3]

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
variable [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

/-- Pointwise Cauchy–Schwarz for the unnormalised operator `U_n`. -/
theorem U_sq_le (n : ℕ) (hn : Adm p n) (F : SectionA3b.Yp p h2 xs ys hxy → ℂ)
    (y : SectionA3b.Yp p h2 xs ys hxy) :
    ‖SectionA4e.U p h2 xs ys hxy n hn.2 F y‖ ^ 2
      ≤ 24 * (Section79a.sg n : ℝ) *
        (SectionA4e.U p h2 xs ys hxy n hn.2 (fun z => ((‖F z‖ ^ 2 : ℝ) : ℂ)) y).re := by
  refine Quotient.inductionOn y (fun g => ?_)
  rw [SectionA4e.U_mk, SectionA4e.U_mk]
  have hcard : (((Section77a.Hn_finite n).toFinset.card : ℕ) : ℝ) = 24 * (Section79a.sg n : ℝ) := by
    have e : ((Section77a.Hn_finite n).toFinset.card) = (Section75a.Hn n).ncard := by
      rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    rw [e, Section79b.h_eq n (Nat.odd_iff.1 hn.1)]
    push_cast; ring
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [← hcard]
  exact sq_norm_sum_le _ _

/-- Pointwise Cauchy–Schwarz for the normalised operator `T_n = U_n / 24`. -/
theorem Tn_sq_le (n : ℕ) (hn : Adm p n) (F : SectionA3b.Yp p h2 xs ys hxy → ℂ)
    (y : SectionA3b.Yp p h2 xs ys hxy) :
    ‖SectionA4g.Tn p h2 xs ys hxy n hn.2 F y‖ ^ 2
      ≤ (Section79a.sg n : ℝ) *
        (SectionA4g.Tn p h2 xs ys hxy n hn.2 (fun z => ((‖F z‖ ^ 2 : ℝ) : ℂ)) y).re := by
  have h := U_sq_le p h2 xs ys hxy n hn F y
  unfold SectionA4g.Tn
  have hn24 : ‖(24 : ℂ)‖ = 24 := by first | simp | norm_num
  have hre : ((SectionA4e.U p h2 xs ys hxy n hn.2 (fun z => ((‖F z‖ ^ 2 : ℝ) : ℂ)) y) / 24).re
      = (SectionA4e.U p h2 xs ys hxy n hn.2 (fun z => ((‖F z‖ ^ 2 : ℝ) : ℂ)) y).re / 24 := by
    first
    | exact Complex.div_ofNat_re _ _
    | (rw [show ((24 : ℂ)) = ((24 : ℝ) : ℂ) by norm_num]; exact Complex.div_ofReal_re _ _)
  rw [norm_div, hn24, div_pow, hre]
  have hσ : (0 : ℝ) ≤ (Section79a.sg n : ℝ) := Nat.cast_nonneg _
  nlinarith [h, hσ]

/-- UNCONDITIONAL Schur bound: `‖T_n f‖ ≤ σ(n) ‖f‖` on all of `L²(Y_p)`. -/
theorem Tl_norm_le (n : ℕ) (hn : Adm p n) (f : EY p h2 xs ys hxy) :
    ‖Tl p h2 xs ys hxy n f‖ ≤ (Section79a.sg n : ℝ) * ‖f‖ := by
  have hσ0 : (0 : ℝ) ≤ (Section79a.sg n : ℝ) := Nat.cast_nonneg _
  -- T_n 1 = σ(n) 1
  have hT1 : Tl p h2 xs ys hxy n (oneY p h2 xs ys hxy)
      = ((Section79a.sg n : ℝ) : ℂ) • oneY p h2 xs ys hxy := by
    ext y
    rw [Tl_apply p h2 xs ys hxy n hn]
    simp only [oneY, PiLp.smul_apply, smul_eq_mul, mul_one]
    rw [SectionA4j.Tn_const p h2 xs ys hxy n (Nat.odd_iff.1 hn.1) hn.2 y]
    push_cast; rfl
  -- G = |f|^2 as an element of L^2
  set G : EY p h2 xs ys hxy := WithLp.toLp 2 (fun z => ((‖f.ofLp z‖ ^ 2 : ℝ) : ℂ)) with hG
  -- the sum of T_n G equals σ(n) times the sum of G  (self-adjointness against 1)
  have hsum : ∑ y, (Tl p h2 xs ys hxy n G).ofLp y = ((Section79a.sg n : ℝ) : ℂ) * ∑ y, G.ofLp y := by
    have e := Tl_symm p h2 xs ys hxy n hn (oneY p h2 xs ys hxy) G
    rw [hT1] at e
    simp only [PiLp.inner_apply, RCLike.inner_apply, oneY, PiLp.smul_apply, smul_eq_mul, map_mul,
      map_one, mul_one, Complex.conj_ofReal] at e
    rw [Finset.mul_sum]
    first
    | exact Eq.trans e.symm (Finset.sum_congr rfl (fun y _ => by ring))
    | (rw [← e]; exact Finset.sum_congr rfl (fun y _ => by ring))
  have hGsum : ∑ y, G.ofLp y = ((∑ y, ‖f.ofLp y‖ ^ 2 : ℝ) : ℂ) := by
    simp [hG, Complex.ofReal_sum]
  have hpt : ∀ y, ‖(Tl p h2 xs ys hxy n f).ofLp y‖ ^ 2
      ≤ (Section79a.sg n : ℝ) * ((Tl p h2 xs ys hxy n G).ofLp y).re := by
    intro y
    rw [Tl_apply p h2 xs ys hxy n hn, Tl_apply p h2 xs ys hxy n hn]
    exact Tn_sq_le p h2 xs ys hxy n hn f.ofLp y
  have hnormsq : ‖Tl p h2 xs ys hxy n f‖ ^ 2 ≤ ((Section79a.sg n : ℝ) * ‖f‖) ^ 2 := by
    have hf : ‖f‖ ^ 2 = ∑ y, ‖f.ofLp y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq] <;> rfl
    rw [mul_pow, hf, EuclideanSpace.norm_sq_eq]
    calc ∑ y, ‖(Tl p h2 xs ys hxy n f).ofLp y‖ ^ 2
        ≤ ∑ y, (Section79a.sg n : ℝ) * ((Tl p h2 xs ys hxy n G).ofLp y).re :=
          Finset.sum_le_sum (fun y _ => hpt y)
      _ = (Section79a.sg n : ℝ) * (∑ y, (Tl p h2 xs ys hxy n G).ofLp y).re := by
          rw [← Finset.mul_sum, ← Complex.re_sum]
      _ = (Section79a.sg n : ℝ) ^ 2 * ∑ y, ‖f.ofLp y‖ ^ 2 := by
          rw [hsum, hGsum, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  have hb : 0 ≤ (Section79a.sg n : ℝ) * ‖f‖ := mul_nonneg hσ0 (norm_nonneg _)
  by_contra hcon
  push_neg at hcon
  nlinarith [hnormsq, hb, hcon, norm_nonneg (Tl p h2 xs ys hxy n f)]

/-- For a prime `l`, `σ(l) = l + 1`. -/
theorem sg_prime {l : ℕ} (hl : l.Prime) : (Section79a.sg l : ℝ) = (l : ℝ) + 1 := by
  have : Section79a.sg l = l + 1 := by
    first
    | (unfold Section79a.sg; rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hl])
    | (unfold Section79a.sg; simp [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hl])
  rw [this]; push_cast; ring

/-- UNCONDITIONAL trivial bound for a prime index: `‖T_l f‖ ≤ (l + 1) ‖f‖`.  It does NOT prove
`HPrime204Restricted` (that needs `≤ (51/25) √l ‖f‖`, a Ramanujan–Petersson statement). -/
theorem Tl_prime_norm_le (l : ℕ) (hl : l.Prime) (hAl : Adm p l) (f : EY p h2 xs ys hxy) :
    ‖Tl p h2 xs ys hxy l f‖ ≤ ((l : ℝ) + 1) * ‖f‖ := by
  have := Tl_norm_le p h2 xs ys hxy l hAl f
  rwa [sg_prime hl] at this

end EDc3

#print axioms EDc3.sq_norm_sum_le
#print axioms EDc3.U_sq_le
#print axioms EDc3.Tn_sq_le
#print axioms EDc3.Tl_norm_le
#print axioms EDc3.Tl_prime_norm_le
