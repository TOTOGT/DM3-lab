import StageA4o

/-!
# EDc6.lean   (UNTESTED until compiled by CI)

A finite, elementary identification.  It proves NOTHING about the size of any eigenvalue and does not touch `RPEigen`.

`EDc4.RPEigen` quantifies over eigenvectors `f` of `T_l` with `⟨1, f⟩ = 0` and `⟨χ, f⟩ = 0`, where `χ(y) = (det g / p)`
(the Legendre symbol of the determinant of any lift `g` of `y`; a value in `{1, -1}` because `det g` is a unit).

The published spectral theorem of Codogni-Lido (J. Number Theory 286 (2026) 131-184, Remark 2.3.6 with Proposition 2.3.7
and Theorem 2.3.8 = 4.18) is stated on the subspace of the vertex space spanned by combinations whose coefficients sum to
zero on each Weil-invariant fibre.  For the scalar level subgroup `H = F_p^× · I` the Weil-invariant set has two elements,
and the fibres should be the two level sets `{χ = 1}`, `{χ = -1}`.  This module proves the Lean side of that bookkeeping:

* `chiY_eq_one_or_neg_one`   : `χ y ∈ {1, -1}` for every `y`.
* `inner_oneY`, `inner_chiE`  : `⟨1, f⟩ = Σ_y f y`, and `⟨χ, f⟩ = Σ_y χ(y) f(y)`.
* `orth_iff_fibre_sums`       : `(⟨1,f⟩ = 0 ∧ ⟨χ,f⟩ = 0)  ↔  (Σ_{χ y = 1} f y = 0 ∧ Σ_{χ y = -1} f y = 0)`.

What this does NOT do: it does not identify `{χ = ±1}` with the Weil-invariant fibres of Codogni-Lido, does not identify
`T_l` with their adjacency matrix, and does not prove or assume their theorem.  Those are the bridges listed in the
specialist package.  `RPEigen` stays OPEN.
-/

namespace EDc6
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
variable [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

/-- `χ` takes only the values `1` and `-1`. -/
theorem chiY_eq_one_or_neg_one (y : SectionA3b.Yp p h2 xs ys hxy) :
    SectionA4k.chiY p h2 xs ys hxy y = 1 ∨ SectionA4k.chiY p h2 xs ys hxy y = -1 := by
  induction y using Quotient.inductionOn with
  | h g =>
    rw [SectionA4k.chiY_mk]
    rcases Int.units_eq_one_or (SectionA4k.chiP p g) with h | h <;> simp [h]

theorem inner_oneY (f : EY p h2 xs ys hxy) :
    inner ℂ (oneY p h2 xs ys hxy) f = ∑ y, f.ofLp y := by
  simp [oneY, PiLp.inner_apply, RCLike.inner_apply]

theorem inner_chiE (f : EY p h2 xs ys hxy) :
    inner ℂ (chiE p h2 xs ys hxy) f = ∑ y, SectionA4k.chiY p h2 xs ys hxy y * f.ofLp y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, chiE]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rcases chiY_eq_one_or_neg_one p h2 xs ys hxy y with h | h <;> simp [h, mul_comm]

open Classical in
/-- Orthogonality to `1` and `χ` is the same as vanishing of the sums of `f` over the two level sets of `χ`. -/
theorem orth_iff_fibre_sums (f : EY p h2 xs ys hxy) :
    (inner ℂ (oneY p h2 xs ys hxy) f = 0 ∧ inner ℂ (chiE p h2 xs ys hxy) f = 0) ↔
      ((∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = 1), f.ofLp y) = 0 ∧
       (∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = -1), f.ofLp y) = 0) := by
  have hne : ¬ ((1 : ℂ) = -1) := by norm_num
  have hne' : ¬ ((-1 : ℂ) = 1) := by norm_num
  set A := ∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = 1), f.ofLp y with hA
  set B := ∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = -1), f.ofLp y with hB
  have hA' : A = ∑ y, (if SectionA4k.chiY p h2 xs ys hxy y = 1 then f.ofLp y else 0) := by
    rw [hA, Finset.sum_filter]
  have hB' : B = ∑ y, (if SectionA4k.chiY p h2 xs ys hxy y = -1 then f.ofLp y else 0) := by
    rw [hB, Finset.sum_filter]
  have h1 : ∑ y, f.ofLp y = A + B := by
    rw [hA', hB', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rcases chiY_eq_one_or_neg_one p h2 xs ys hxy y with h | h <;> simp [h, hne, hne']
  have h2' : ∑ y, SectionA4k.chiY p h2 xs ys hxy y * f.ofLp y = A - B := by
    rw [hA', hB', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rcases chiY_eq_one_or_neg_one p h2 xs ys hxy y with h | h <;> simp [h, hne, hne']
  rw [inner_oneY, inner_chiE, h1, h2']
  constructor
  · rintro ⟨e1, e2⟩
    exact ⟨by linear_combination (1 / 2 : ℂ) * e1 + (1 / 2 : ℂ) * e2,
           by linear_combination (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2⟩
  · rintro ⟨e1, e2⟩
    exact ⟨by rw [e1, e2]; ring, by rw [e1, e2]; ring⟩

end EDc6

#print axioms EDc6.chiY_eq_one_or_neg_one
#print axioms EDc6.inner_oneY
#print axioms EDc6.inner_chiE
#print axioms EDc6.orth_iff_fibre_sums
