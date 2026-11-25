import StageA4o
import EDc6

/-!
# weil_fibre.lean   (DRAFT, UNTESTED: never compiled; CI on GitHub is the only compiler)

Bridge 2, finite algebra only.  Builds on the green module `EDc6` (`orth_iff_fibre_sums`).

Hand derivation.  `chiY (Γ g) = χ(g) ∈ {±1}`, and for `x ∈ Hn n`, `p ∤ n`, `chiP_rhoT` gives
`χ(rhoT x) = (n/p)`, so `χ(Γ · rhoT x · g) = (n/p) χ(Γ g)` (the multiplicativity step is the one used in
`SectionA4k.U_chi`).  `T_n f (Γ g) = (1/24) Σ_{x ∈ Hn n} f(Γ rhoT x g)`.  Hence, if `f` is supported on
`{χ = ε}`, a nonzero value `T_n f (y)` forces some term nonzero, i.e. `(n/p) χ(y) = ε`.  Separately,
`T_n` is symmetric and `1`, `χ` are eigenvectors (`Tl_symm`, `Tl_one_eig`, `Tl_chi_eig`, all in StageA4o), so
`⟨1, T f⟩ = ⟨T 1, f⟩ = conj(a)⟨1, f⟩`, and likewise for `χ`; the orthogonal complement of `{1, χ}` is invariant.

Theorems (labels: all *finite bookkeeping*; none uses `RPEigen`):
* `chiY_rhoT_mul`                 : `χ(Γ · rhoT x · g) = (n/p) · χ(Γ g)` for `x ∈ Hn n`.
* `Tl_support_shift`              : if `f` is supported on `{χ = ε}` and `(T_n f)(y) ≠ 0` then `(n/p)·χ(y) = ε`,
                                    i.e. `T_n f` is supported on `{χ = ε·(n/p)}` (as `(n/p)² = 1`; stated in the
                                    form that avoids needing `(n/p) ∈ {±1}`).
* `Tl_preserves_orth`             : `⟨1,f⟩ = 0 ∧ ⟨χ,f⟩ = 0` is preserved by `T_n`.
* `Tl_preserves_fibre_sums_zero`  : the subspace `{Σ_{χ=1} f = 0 ∧ Σ_{χ=-1} f = 0}` is `T_n`-invariant (via EDc6).

Names checked by grep in StageA4o.lean: Tl, Tl_apply, Tl_symm, Tl_one_eig, Tl_chi_eig, oneY, chiE, EY, Adm,
SectionA4e.U_mk, SectionA4e.rhoT, SectionA4g.Tn, SectionA4k.chiY, chiY_mk, chiP, chiP_rhoT, Section77a.Hn_finite.
Names from Mathlib NOT checked: `Quotient.inductionOn`, `Finset.sum_eq_zero`, `inner_smul_left`, `Set.Finite.mem_toFinset`
(the last three are used in the same form elsewhere in StageA4o/EDc6).

What this does NOT establish: it does NOT identify the Codogni-Lido (Weil-invariant) fibres with the level sets of `χ`
(external, specialist question); it does not say `T_n` is their adjacency matrix; it proves nothing about eigenvalue
size; it does not prove or assume `RPEigen`, which stays OPEN.  `Tl_support_shift` is about `χ`-level sets only.
-/

namespace WeilFibre
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
variable [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

theorem chiY_rhoT_mul {n : ℕ} {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn n) (hpn : ¬ p ∣ n)
    (g : SectionA2.PGL2 p) :
    SectionA4k.chiY p h2 xs ys hxy
        (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
          (SectionA4e.rhoT p xs ys x * g))
      = ((quadraticChar (ZMod p) (n : ZMod p) : ℤ) : ℂ)
        * SectionA4k.chiY p h2 xs ys hxy
          (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g) := by
  rw [SectionA4k.chiY_mk, SectionA4k.chiY_mk, map_mul, Units.val_mul,
    ← SectionA4k.chiP_rhoT p h2 xs ys hxy hx hpn]
  push_cast; ring

/-- If `f` is supported on `{χ = ε}` and `T_n f` is nonzero at `y`, then `(n/p) χ(y) = ε`. -/
theorem Tl_support_shift (n : ℕ) (h : Adm p n) (ε : ℂ) (f : EY p h2 xs ys hxy)
    (hf : ∀ y, SectionA4k.chiY p h2 xs ys hxy y ≠ ε → f.ofLp y = 0)
    (y : SectionA3b.Yp p h2 xs ys hxy)
    (hy : (Tl p h2 xs ys hxy n f).ofLp y ≠ 0) :
    ((quadraticChar (ZMod p) (n : ZMod p) : ℤ) : ℂ) * SectionA4k.chiY p h2 xs ys hxy y = ε := by
  have key : ∀ g : SectionA2.PGL2 p,
      ((quadraticChar (ZMod p) (n : ZMod p) : ℤ) : ℂ) * SectionA4k.chiY p h2 xs ys hxy
          (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g) ≠ ε →
      (Tl p h2 xs ys hxy n f).ofLp
          (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g) = 0 := by
    intro g hg
    rw [Tl_apply p h2 xs ys hxy n h]
    simp only [SectionA4g.Tn]
    rw [SectionA4e.U_mk]
    have hs : ∑ x ∈ (Section77a.Hn_finite n).toFinset,
        f.ofLp (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
          (SectionA4e.rhoT p xs ys x * g)) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      have hx' := (Set.Finite.mem_toFinset _).1 hx
      by_contra hne
      have hc : SectionA4k.chiY p h2 xs ys hxy
          (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
            (SectionA4e.rhoT p xs ys x * g)) = ε := by
        by_contra hc'
        exact hne (hf _ hc')
      apply hg
      rw [← chiY_rhoT_mul p h2 xs ys hxy hx' h.2 g]
      exact hc
    rw [hs]; simp
  revert hy
  induction y using Quotient.inductionOn with
  | h g =>
    intro hy
    by_contra hne
    exact hy (key g hne)

/-- `T_n` preserves orthogonality to `1` and to `χ` (symmetry plus eigenvector property). -/
theorem Tl_preserves_orth (n : ℕ) (h : Adm p n) (f : EY p h2 xs ys hxy)
    (hf : inner ℂ (oneY p h2 xs ys hxy) f = 0 ∧ inner ℂ (chiE p h2 xs ys hxy) f = 0) :
    inner ℂ (oneY p h2 xs ys hxy) (Tl p h2 xs ys hxy n f) = 0 ∧
      inner ℂ (chiE p h2 xs ys hxy) (Tl p h2 xs ys hxy n f) = 0 := by
  obtain ⟨a, ha⟩ := Tl_one_eig p h2 xs ys hxy n h
  obtain ⟨b, hb⟩ := Tl_chi_eig p h2 xs ys hxy n h
  have hs := Tl_symm p h2 xs ys hxy n h
  constructor
  · have e := hs (oneY p h2 xs ys hxy) f
    rw [← e, ha, inner_smul_left, hf.1]; simp
  · have e := hs (chiE p h2 xs ys hxy) f
    rw [← e, hb, inner_smul_left, hf.2]; simp

open Classical in
/-- The fibre-sum-zero subspace of `EDc6.orth_iff_fibre_sums` is `T_n`-invariant. -/
theorem Tl_preserves_fibre_sums_zero (n : ℕ) (h : Adm p n) (f : EY p h2 xs ys hxy)
    (hf : (∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = 1), f.ofLp y) = 0 ∧
       (∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = -1), f.ofLp y) = 0) :
    (∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = 1),
        (Tl p h2 xs ys hxy n f).ofLp y) = 0 ∧
    (∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = -1),
        (Tl p h2 xs ys hxy n f).ofLp y) = 0 :=
  (EDc6.orth_iff_fibre_sums p h2 xs ys hxy (Tl p h2 xs ys hxy n f)).1
    (Tl_preserves_orth p h2 xs ys hxy n h f
      ((EDc6.orth_iff_fibre_sums p h2 xs ys hxy f).2 hf))

end WeilFibre

#print axioms WeilFibre.chiY_rhoT_mul
#print axioms WeilFibre.Tl_support_shift
#print axioms WeilFibre.Tl_preserves_orth
#print axioms WeilFibre.Tl_preserves_fibre_sums_zero
