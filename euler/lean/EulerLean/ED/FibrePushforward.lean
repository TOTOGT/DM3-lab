import EDc6

/-!
Finite fibre-pushforward transport for the Codogni--Lido interface.
This file proves no geometric identification and no spectral bound.
`RPEigen` remains open. Verification evidence is in the lane handoff.
-/

namespace EulerWeilFibre

open Classical in
noncomputable def fibrePush {V I : Type*} [Fintype V] [DecidableEq I] (w : V → I) :
    (V → ℂ) →ₗ[ℂ] (I → ℂ) where
  toFun f i := ∑ v ∈ Finset.univ.filter (fun v => w v = i), f v
  map_add' f g := by ext i; simp [Finset.sum_add_distrib]
  map_smul' c f := by ext i; simp [Finset.mul_sum]

open Classical in
theorem mem_ker_fibrePush {V I : Type*} [Fintype V] [DecidableEq I] (w : V → I) (f : V → ℂ) :
    f ∈ LinearMap.ker (fibrePush w) ↔
      ∀ i, (∑ v ∈ Finset.univ.filter (fun v => w v = i), f v) = 0 := by
  change (fun i => ∑ v ∈ Finset.univ.filter (fun v => w v = i), f v) =
    (fun _ => (0 : ℂ)) ↔ _
  exact funext_iff

open Classical in
theorem fibre_sum_reindex {Y V I : Type*} [Fintype Y] [Fintype V] [DecidableEq I]
    (e : Y ≃ V) (w : V → I) (i : I) (f : Y → ℂ) :
    (∑ v ∈ Finset.univ.filter (fun v => w v = i), f (e.symm v)) =
      ∑ y ∈ Finset.univ.filter (fun y => w (e y) = i), f y := by
  simp only [Finset.sum_filter]
  exact Fintype.sum_equiv e.symm _ _ (fun v => by simp)

open Classical in
theorem fibrePush_relabel {V I J : Type*} [Fintype V] [DecidableEq I] [DecidableEq J]
    (s : I ≃ J) (w : V → I) (f : V → ℂ) :
    fibrePush (s ∘ w) f = (fibrePush w f) ∘ s.symm := by
  ext j
  change (∑ v ∈ Finset.univ.filter (fun v => s (w v) = j), f v) =
    ∑ v ∈ Finset.univ.filter (fun v => w v = s.symm j), f v
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro v _
  constructor
  · intro h
    simpa using congrArg s.symm h
  · intro h
    rw [h, s.apply_symm_apply]

theorem ker_fibrePush_relabel {V I J : Type*} [Fintype V] [DecidableEq I] [DecidableEq J]
    (s : I ≃ J) (w : V → I) :
    LinearMap.ker (fibrePush (s ∘ w)) = LinearMap.ker (fibrePush w) := by
  ext f
  simp only [LinearMap.mem_ker, fibrePush_relabel]
  constructor
  · intro h
    ext i
    have hi := congrFun h (s i)
    simpa using hi
  · intro h
    rw [h]
    rfl

open SectionA4m2

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
variable [Fintype (SectionA2.PGL2 p)]
  [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

open Classical in
theorem orth_iff_mem_ker_fibrePush
    {V : Type*} [Fintype V]
    (e : SectionA3b.Yp p h2 xs ys hxy ≃ V) (w : V → Bool)
    (hw : ∀ y, w (e y) = true ↔ SectionA4k.chiY p h2 xs ys hxy y = 1)
    (f : EY p h2 xs ys hxy) :
    (inner ℂ (oneY p h2 xs ys hxy) f = 0 ∧
      inner ℂ (chiE p h2 xs ys hxy) f = 0) ↔
      (fun v => f.ofLp (e.symm v)) ∈ LinearMap.ker (fibrePush w) := by
  classical
  have hfalse (y : SectionA3b.Yp p h2 xs ys hxy) :
      w (e y) = false ↔ SectionA4k.chiY p h2 xs ys hxy y = -1 := by
    constructor
    · intro hf
      rcases EDc6.chiY_eq_one_or_neg_one p h2 xs ys hxy y with hc | hc
      · have ht := (hw y).mpr hc
        rw [hf] at ht
        cases ht
      · exact hc
    · intro hc
      cases hb : w (e y)
      · rfl
      · have he := (hw y).mp hb
        have : (1 : ℂ) = -1 := he.symm.trans hc
        norm_num at this
  have htrue_sum :
      (∑ v ∈ Finset.univ.filter (fun v => w v = true), f.ofLp (e.symm v)) =
        ∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = 1), f.ofLp y := by
    simpa only [Finset.sum_filter, hw] using
      (fibre_sum_reindex e w true (fun y => f.ofLp y))
  have hfalse_sum :
      (∑ v ∈ Finset.univ.filter (fun v => w v = false), f.ofLp (e.symm v)) =
        ∑ y ∈ Finset.univ.filter (fun y => SectionA4k.chiY p h2 xs ys hxy y = -1), f.ofLp y := by
    simpa only [Finset.sum_filter, hfalse] using
      (fibre_sum_reindex e w false (fun y => f.ofLp y))
  rw [EDc6.orth_iff_fibre_sums p h2 xs ys hxy f, mem_ker_fibrePush]
  constructor
  · rintro ⟨hp, hn⟩ b
    cases b
    · simpa only [Finset.sum_filter] using hfalse_sum.trans hn
    · simpa only [Finset.sum_filter] using htrue_sum.trans hp
  · intro hf
    constructor
    · apply htrue_sum.symm.trans
      simpa only [Finset.sum_filter] using hf true
    · apply hfalse_sum.symm.trans
      simpa only [Finset.sum_filter] using hf false

open Classical in
/-- The two Weil labels may be interchanged without changing the kernel. -/
theorem orth_iff_mem_ker_fibrePush_swap
    {V : Type*} [Fintype V]
    (e : SectionA3b.Yp p h2 xs ys hxy ≃ V) (w : V → Bool)
    (hw : ∀ y, w (e y) = true ↔ SectionA4k.chiY p h2 xs ys hxy y = 1)
    (f : EY p h2 xs ys hxy) :
    (inner ℂ (oneY p h2 xs ys hxy) f = 0 ∧
      inner ℂ (chiE p h2 xs ys hxy) f = 0) ↔
      (fun v => f.ofLp (e.symm v)) ∈
        LinearMap.ker (fibrePush (Equiv.boolNot ∘ w)) := by
  rw [ker_fibrePush_relabel]
  exact orth_iff_mem_ker_fibrePush p h2 xs ys hxy e w hw f

end EulerWeilFibre

#print axioms EulerWeilFibre.fibre_sum_reindex
#print axioms EulerWeilFibre.fibrePush_relabel
#print axioms EulerWeilFibre.ker_fibrePush_relabel
#print axioms EulerWeilFibre.orth_iff_mem_ker_fibrePush

#print axioms EulerWeilFibre.orth_iff_mem_ker_fibrePush_swap
#print axioms EulerWeilFibre.mem_ker_fibrePush

#check EulerWeilFibre.mem_ker_fibrePush

#check EulerWeilFibre.fibre_sum_reindex

#check EulerWeilFibre.fibrePush_relabel

#check EulerWeilFibre.ker_fibrePush_relabel

#check EulerWeilFibre.orth_iff_mem_ker_fibrePush

#check EulerWeilFibre.orth_iff_mem_ker_fibrePush_swap
