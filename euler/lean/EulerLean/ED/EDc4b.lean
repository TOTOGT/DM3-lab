import EDcDefs

/-!
# EDc4b.lean   (UNTESTED until compiled by CI)

Parallel variant of EDc4 with the same mathematical content and a different Lean structure, run alongside EDc4 so
that one CI push tests both elaboration routes.  EDc4 failed twice on ELABORATION (not mathematics): the restricted
operator was built inline on a `let`-bound submodule.  Here the restriction step is isolated in a generic lemma
`norm_le_on_invariant` stated for an arbitrary invariant submodule `V`, with no `let` and no `Tl` in sight; the
`Tl`-specific proof then only supplies `V`, invariance and the eigenvalue bound.

* `norm_le_of_eigen_bound` : the spectral lemma, copied verbatim from EDc4 (it compiled with axioms
  `[propext, Classical.choice, Quot.sound]` on `ff2ff49` and `4e322fc`).
* `norm_le_on_invariant` : for a symmetric `T`, an invariant submodule `V`, and a bound `B` on the real eigenvalues of
  `T` having eigenvectors in `V`, `‖T f‖ ≤ B ‖f‖` for `f ∈ V`.
* `RPEigen` : the eigenvalue-level Ramanujan hypothesis, same statement as `EDc4.RPEigen`.  OPEN.  Not proved in this
  development.
* `hprime204_of_rpeigen : RPEigen → HPrime204Restricted`.

Same disclaimers as EDc4: nothing here proves `RPEigen`; the constant 2 lives inside it.
-/

namespace EDc4b
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

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

/-- The same bound for vectors of an invariant submodule, given an eigenvalue bound on that submodule. -/
theorem norm_le_on_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (V : Submodule ℂ E) (hV : ∀ v ∈ V, T v ∈ V)
    (B : ℝ) (hB : 0 ≤ B)
    (hev : ∀ (μ : ℝ) (v : E), v ∈ V → v ≠ 0 → T v = (μ : ℂ) • v → |μ| ≤ B)
    (f : E) (hf : f ∈ V) : ‖T f‖ ≤ B * ‖f‖ := by
  have hT' : (T.restrict hV).IsSymmetric := hT.restrict_invariant hV
  have hev' : ∀ (μ : ℝ) (v : V), v ≠ 0 → (T.restrict hV) v = (μ : ℂ) • v → |μ| ≤ B := by
    intro μ v hv0 hv
    refine hev μ (v : E) v.2 ?_ ?_
    · intro h
      exact hv0 (Subtype.ext h)
    · have h' := congrArg Subtype.val hv
      simpa using h'
  have key : ‖(T.restrict hV) (⟨f, hf⟩ : V)‖ ≤ B * ‖(⟨f, hf⟩ : V)‖ :=
    norm_le_of_eigen_bound (T.restrict hV) hT' B hB hev' ⟨f, hf⟩
  have e1 : ‖(T.restrict hV) (⟨f, hf⟩ : V)‖ = ‖T f‖ := by
    first
    | (rw [← Submodule.coe_norm]; rfl)
    | simp [Submodule.coe_norm]
  have e2 : ‖(⟨f, hf⟩ : V)‖ = ‖f‖ := by
    first
    | rfl
    | simp
  rw [e1, e2] at key
  exact key

open Classical in
/-- Eigenvalue-level Ramanujan hypothesis; identical to `EDc4.RPEigen`.  EXTERNAL, OPEN. -/
def RPEigen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_hp3 : p % 4 = 3) (_hp4 : 3 < p) (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (l : ℕ), l.Prime → l % 4 = 3 → Adm p l →
    ∀ (μ : ℝ) (f : EY p h2 xs ys hxy), f ≠ 0 →
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      Tl p h2 xs ys hxy l f = (μ : ℂ) • f → |μ| ≤ 2 * Real.sqrt l

open Classical in
theorem hprime204_of_rpeigen (hR : RPEigen) : EDcDefs.HPrime204Restricted := by
  intro p _ hp3 hp4 h2 xs ys hxy l hl hl4 hAdm f h1 hchi
  have hsymm : (Tl p h2 xs ys hxy l).IsSymmetric := Tl_symm p h2 xs ys hxy l hAdm
  obtain ⟨a, ha⟩ := Tl_one_eig p h2 xs ys hxy l hAdm
  obtain ⟨b, hb⟩ := Tl_chi_eig p h2 xs ys hxy l hAdm
  have hmem : ∀ v : EY p h2 xs ys hxy,
      v ∈ (Submodule.span ℂ {oneY p h2 xs ys hxy})ᗮ ⊓ (Submodule.span ℂ {chiE p h2 xs ys hxy})ᗮ ↔
      (inner ℂ (oneY p h2 xs ys hxy) v = 0 ∧ inner ℂ (chiE p h2 xs ys hxy) v = 0) := by
    intro v
    simp only [Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinv : ∀ v ∈ (Submodule.span ℂ {oneY p h2 xs ys hxy})ᗮ ⊓
      (Submodule.span ℂ {chiE p h2 xs ys hxy})ᗮ, Tl p h2 xs ys hxy l v ∈
      (Submodule.span ℂ {oneY p h2 xs ys hxy})ᗮ ⊓ (Submodule.span ℂ {chiE p h2 xs ys hxy})ᗮ := by
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
  have hB : (0 : ℝ) ≤ 2 * Real.sqrt l := by positivity
  have key := norm_le_on_invariant (Tl p h2 xs ys hxy l) hsymm
    ((Submodule.span ℂ {oneY p h2 xs ys hxy})ᗮ ⊓ (Submodule.span ℂ {chiE p h2 xs ys hxy})ᗮ) hinv
    (2 * Real.sqrt l) hB
    (fun μ v hv hv0 hTv => by
      have hv' := (hmem v).1 hv
      exact hR p hp3 hp4 h2 xs ys hxy l hl hl4 hAdm μ v hv0 hv'.1 hv'.2 hTv)
    f ((hmem f).2 ⟨h1, hchi⟩)
  have hnn : 0 ≤ Real.sqrt l * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [key, hnn]

end EDc4b

#print axioms EDc4b.norm_le_of_eigen_bound
#print axioms EDc4b.norm_le_on_invariant
#print axioms EDc4b.hprime204_of_rpeigen
