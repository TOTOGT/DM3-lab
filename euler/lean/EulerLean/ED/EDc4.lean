import EDcDefs

/-!
# EDc4.lean   (UNTESTED until compiled by CI)

Phase 8D.  The INTERFACE between the external Ramanujan-Petersson theorem and `EDcDefs.HPrime204Restricted`.

`HPrime204Restricted` is an operator-norm statement: `‖T_l f‖ ≤ (51/25) √l ‖f‖` for every `f ⟂ {1, χ}`.
A Ramanujan-Petersson theorem (via Jacquet-Langlands and Eichler-Shimura + Weil/Deligne) does not deliver that
directly.  It delivers a statement about EIGENVALUES: every eigenvalue of `T_l` on the orthogonal complement of
`span{1, χ}` is a Hecke eigenvalue `a_l` of a weight-2 cusp form, hence `|a_l| ≤ 2 √l`.

* `RPEigen` : the eigenvalue-level statement, exactly in that shape (for every real `μ` and every nonzero `f`
  with `f ⟂ 1`, `f ⟂ χ` and `T_l f = μ f`, `|μ| ≤ 2 √l`).  It is a HYPOTHESIS (a `def : Prop`).  It is EXTERNAL and
  NOT PROVED here.
* `norm_le_of_eigen_bound` : PROVED (pure linear algebra).  For a symmetric operator on a finite-dimensional complex
  inner product space, a bound `B` on every real eigenvalue gives `‖T f‖ ≤ B ‖f‖`.  (Spectral theorem + Parseval.)
* `hprime204_of_rpeigen` : PROVED.  `RPEigen → HPrime204Restricted`.  Steps: the complement
  `W = {1, χ}^⊥` is `T_l`-invariant (`T_l` symmetric, `1` and `χ` are eigenvectors); `T_l|_W` is symmetric; every
  eigenvector of `T_l|_W` is an eigenvector of `T_l` orthogonal to `1` and `χ`, so `RPEigen` bounds its eigenvalue by
  `2 √l`; the spectral lemma gives `‖T_l f‖ ≤ 2 √l ‖f‖ ≤ (51/25) √l ‖f‖`.

What this changes.  The open hypothesis is no longer an operator-norm bound; it is the eigenvalue statement
`RPEigen`, which is the form the specialist theorem actually has.  The constant improves from `51/25` to the true
Ramanujan constant `2`.

What this does NOT do.  It does not prove `RPEigen`.  `RPEigen` is OPEN here.  Its content is: Jacquet-Langlands
(the eigenvalues on `{1, χ}^⊥` are `a_l` of weight-2 cusp forms, trivial character, level dividing `2 p²`) plus the
Ramanujan-Petersson bound for those forms (Eichler-Shimura + Weil/Deligne), plus the component count showing that
`W` contains no eigenvector with eigenvalue `±(l+1)`.  Mathlib has none of these.  `HPrime204Restricted` stays
conditional on `RPEigen`.
-/

namespace EDc4
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

/-- Spectral reduction.  A symmetric operator on a finite-dimensional complex inner product space whose real
eigenvalues are all bounded by `B` has operator norm at most `B`. -/
theorem norm_le_of_eigen_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (B : ℝ) (hB : 0 ≤ B)
    (hev : ∀ (μ : ℝ) (v : E), v ≠ 0 → T v = (μ : ℂ) • v → |μ| ≤ B) (f : E) :
    ‖T f‖ ≤ B * ‖f‖ := by
  set n := Module.finrank ℂ E with hn
  set b := hT.eigenvectorBasis (n := n) rfl with hbdef
  have hTb : ∀ i, T (b i) = ((hT.eigenvalues (n := n) rfl i : ℝ) : ℂ) • b i :=
    fun i => hT.apply_eigenvectorBasis rfl i
  have hmu : ∀ i, |hT.eigenvalues (n := n) rfl i| ≤ B := by
    intro i
    refine hev _ (b i) ?_ (hTb i)
    intro h0
    have h1 := b.orthonormal.1 i
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  set c : Fin n → ℂ := fun i => (b.repr f).ofLp i with hc
  have hf : f = ∑ i, c i • b i := (b.sum_repr f).symm
  have hTf : T f = ∑ i, (c i * ((hT.eigenvalues (n := n) rfl i : ℝ) : ℂ)) • b i := by
    conv_lhs => rw [hf]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hTb, smul_smul]
  have hinner : ∀ (a : Fin n → ℂ) (i : Fin n), inner ℂ (b i) (∑ j, a j • b j) = a i := by
    intro a i
    rw [inner_sum]
    simp only [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal]
    simp
  have hnormsq : ∀ (a : Fin n → ℂ), ‖∑ j, a j • b j‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    intro a
    rw [← b.sum_sq_norm_inner_right]
    exact (Finset.sum_congr rfl (fun i _ => by rw [hinner])).symm
  have h1 : ‖T f‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 * |hT.eigenvalues (n := n) rfl i| ^ 2 := by
    rw [hTf, hnormsq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖f‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have := hnormsq c
    rwa [← hf] at this
  have h3 : ‖T f‖ ^ 2 ≤ (B * ‖f‖) ^ 2 := by
    rw [h1, mul_pow, h2, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h4 : |hT.eigenvalues (n := n) rfl i| ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hmu i) 2
    nlinarith [sq_nonneg ‖c i‖]
  exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (mul_nonneg hB (norm_nonneg _)))

open Classical in
/-- The EIGENVALUE-level Ramanujan statement for `T_l` on `L²(Y_p)` ⊖ `span{1, χ}`: every real eigenvalue of `T_l`
with an eigenvector orthogonal to `1` and `χ` has absolute value at most `2 √l`.  EXTERNAL HYPOTHESIS, OPEN here:
it needs Jacquet-Langlands, the weight-2 Ramanujan-Petersson bound, and the component count (no `±(l+1)` on the
complement).  Same data `(p, xs, ys)`, same side conditions as `EDcDefs.HPrime204Restricted`. -/
def RPEigen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_hp3 : p % 4 = 3) (_hp4 : 3 < p) (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (l : ℕ), l.Prime → l % 4 = 3 → Adm p l →
    ∀ (μ : ℝ) (f : EY p h2 xs ys hxy), f ≠ 0 →
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      Tl p h2 xs ys hxy l f = (μ : ℂ) • f → |μ| ≤ 2 * Real.sqrt l

open Classical in
/-- `RPEigen` implies the operator-norm hypothesis `HPrime204Restricted` (with room to spare: `2 ≤ 51/25`). -/
theorem hprime204_of_rpeigen (hR : RPEigen) : EDcDefs.HPrime204Restricted := by
  intro p _ hp3 hp4 h2 xs ys hxy l hl hl4 hAdm f h1 hchi
  have hsymm : (Tl p h2 xs ys hxy l).IsSymmetric := Tl_symm p h2 xs ys hxy l hAdm
  obtain ⟨a, ha⟩ := Tl_one_eig p h2 xs ys hxy l hAdm
  obtain ⟨b, hb⟩ := Tl_chi_eig p h2 xs ys hxy l hAdm
  let W : Submodule ℂ (EY p h2 xs ys hxy) :=
    (Submodule.span ℂ {oneY p h2 xs ys hxy})ᗮ ⊓ (Submodule.span ℂ {chiE p h2 xs ys hxy})ᗮ
  have hmem : ∀ v, v ∈ W ↔
      (inner ℂ (oneY p h2 xs ys hxy) v = 0 ∧ inner ℂ (chiE p h2 xs ys hxy) v = 0) := by
    intro v
    simp only [W, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinv : ∀ v ∈ W, Tl p h2 xs ys hxy l v ∈ W := by
    intro v hv
    rw [hmem] at hv ⊢
    obtain ⟨hv1, hv2⟩ := hv
    constructor
    · have e := hsymm (oneY p h2 xs ys hxy) v
      rw [ha, inner_smul_left, hv1, mul_zero] at e
      exact e.symm
    · have e := hsymm (chiE p h2 xs ys hxy) v
      rw [hb, inner_smul_left, hv2, mul_zero] at e
      exact e.symm
  have hT' : ((Tl p h2 xs ys hxy l).restrict hinv).IsSymmetric := hsymm.restrict_invariant hinv
  have hfW : f ∈ W := (hmem f).2 ⟨h1, hchi⟩
  have hB : (0 : ℝ) ≤ 2 * Real.sqrt l := by positivity
  have hev : ∀ (μ : ℝ) (v : W), v ≠ 0 →
      (Tl p h2 xs ys hxy l).restrict hinv v = (μ : ℂ) • v → |μ| ≤ 2 * Real.sqrt l := by
    intro μ v hv0 hv
    refine hR p hp3 hp4 h2 xs ys hxy l hl hl4 hAdm μ (v : EY p h2 xs ys hxy) ?_ ?_ ?_ ?_
    · intro h
      exact hv0 (Subtype.ext h)
    · exact ((hmem v).1 v.2).1
    · exact ((hmem v).1 v.2).2
    · have h' := congrArg Subtype.val hv
      simpa using h'
  have key := norm_le_of_eigen_bound ((Tl p h2 xs ys hxy l).restrict hinv) hT' _ hB hev ⟨f, hfW⟩
  have e1 : ‖(Tl p h2 xs ys hxy l).restrict hinv ⟨f, hfW⟩‖ = ‖Tl p h2 xs ys hxy l f‖ := by
    first
    | (rw [← Submodule.coe_norm]; rfl)
    | simp [Submodule.coe_norm]
  have e2 : ‖(⟨f, hfW⟩ : W)‖ = ‖f‖ := by
    first
    | rfl
    | simp
  rw [e1, e2] at key
  have hnn : 0 ≤ Real.sqrt l * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [key, hnn]

end EDc4

#print axioms EDc4.norm_le_of_eigen_bound
#print axioms EDc4.hprime204_of_rpeigen
