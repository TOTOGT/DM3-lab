import EDc10
import VertexDoubleOrbit
import FibrePushforward
import EDc8
import EDc9

/-!
# ScalarDescent.lean   — UNTESTED (never compiled; no Lean/Mathlib toolchain was available when written)

STATUS LABELS used below:  [HAND] hand-checked mathematics, [SRC] matched by reading the pinned source export,
[UNTESTED] Lean text never elaborated, [GAP] proof not written (marked `sorry`; must NOT be counted as closed).

WHAT THIS FILE IS: the finite "scalar descent" bridge between the FULL-LEVEL vertex set
  FullLevel = U \ GL2(F_p)        (U = image of the 24 Hurwitz units under the matrix reduction)
and the projective vertex set  Yp = Gam \ PGL2(F_p).  It proves (if it compiles) only finite bookkeeping:
  * unitRedHom : HurU →* GL2(F_p), fullDet, project : FullLevel → Yp, surjectivity;
  * for each determinant a, project restricts to a bijection {fullDet = a} ≃ {χ = χ(a)}   (detFibreEquiv);
  * pullback of a vector orthogonal to 1 and χ has zero sum on every determinant fibre (Weil-kernel membership);
  * full-level Hecke operator, defined independently of the projective one (GAP: well-definedness, intertwining);
  * a CONDITIONAL transport: a bound on the full-level operator on the Weil kernel ⇒ `RPEigenAt` at (p,xs,ys).
WHAT IT DOES NOT DO: it does not prove the geometric dictionary or the spectral bound |μ| ≤ 2√ℓ.  That bound is
the explicit hypothesis `FullLevelBound`.  RPEigen is not assumed, renamed, or closed here.
No axioms, no native_decide.  `sorry`s are exactly the declarations tagged [GAP].
-/

namespace EulerScalarDescent
open EulerVertexDraft SectionA4m2 SectionA4k

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1)

/-! ### 1. The unit reduction as a bundled homomorphism  [SRC: unitRed, Section74b.red_mul, red_one] -/

theorem unitRed_val (u : SectionA3a2.HurU) :
    ((unitRed p h2 xs ys hxy u : MatrixUnits p) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      Section74b.red p xs ys (((u : (Quaternion ℚ)ˣ)) : Quaternion ℚ) := by
  unfold unitRed
  rw [SectionA2.redUnit_coe]

theorem unitRed_det_one (u : SectionA3a2.HurU) :
    Matrix.det ((unitRed p h2 xs ys hxy u : MatrixUnits p) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
  have hu := (SectionA3a2.mem_iff _).mp u.2
  rw [unitRed_val]
  have hd := Section74c.det_red p h2 xs ys hxy hu.1 1 (by rw [hu.2]; norm_num)
  simpa using hd

noncomputable def unitRedHom : SectionA3a2.HurU →* MatrixUnits p where
  toFun := unitRed p h2 xs ys hxy
  map_one' := by
    apply Units.ext
    rw [unitRed_val]
    simpa using Section74b.red_one p h2 xs ys
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mul, unitRed_val, unitRed_val, unitRed_val]
    have ha := (SectionA3a2.mem_iff _).mp a.2
    have hb := (SectionA3a2.mem_iff _).mp b.2
    simpa using Section74b.red_mul p h2 xs ys hxy ha.1 hb.1

theorem unitRedHom_apply (u : SectionA3a2.HurU) :
    unitRedHom p h2 xs ys hxy u = unitRed p h2 xs ys hxy u := rfl

/-- `unitRed (-1) = -1` as a matrix unit.  [SRC: StageA4o.red_negone] -/
theorem unitRed_negOne :
    unitRed p h2 xs ys hxy SectionA3a2.negOne = (-1 : MatrixUnits p) := by
  apply Units.ext
  rw [unitRed_val]
  have : ((((SectionA3a2.negOne : SectionA3a2.HurU) : (Quaternion ℚ)ˣ)) : Quaternion ℚ) = -1 := rfl
  rw [this, SectionA4o.red_negone p h2 xs ys]
  simp

/-! ### 2. Full-level vertex set, determinant, projection -/

/-- Full-level vertices: right cosets (= left orbits) of the unit image U in GL2(F_p).  NOT `liftedGamma`
(which contains the centre). -/
abbrev FullLevel : Type :=
  Quotient (QuotientGroup.rightRel (unitRedHom p h2 xs ys hxy).range)

noncomputable instance : Finite (FullLevel p h2 xs ys hxy) := Quotient.finite _
noncomputable instance : Fintype (FullLevel p h2 xs ys hxy) := Fintype.ofFinite _

theorem fullRel_iff (a b : MatrixUnits p) :
    QuotientGroup.rightRel (unitRedHom p h2 xs ys hxy).range a b ↔
      ∃ u : SectionA3a2.HurU, unitRed p h2 xs ys hxy u * a = b := by
  rw [QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have : unitRedHom p h2 xs ys hxy u = b * a⁻¹ := hu
    rw [unitRedHom_apply] at this
    rw [this]; group
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [unitRedHom_apply]; group

/-- Determinant of a matrix unit, valued in `(ZMod p)ˣ`. -/
noncomputable def detU : MatrixUnits p →* (ZMod p)ˣ := Matrix.GeneralLinearGroup.det

theorem detU_val (g : MatrixUnits p) :
    ((detU p g : (ZMod p)ˣ) : ZMod p) = Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  simp [detU]   -- UNTESTED: may need `Matrix.GeneralLinearGroup.val_det_apply`

theorem detU_unitRed (u : SectionA3a2.HurU) : detU p (unitRed p h2 xs ys hxy u) = 1 := by
  apply Units.ext
  rw [detU_val, unitRed_det_one p h2 xs ys hxy]; rfl

noncomputable def fullDet : FullLevel p h2 xs ys hxy → (ZMod p)ˣ :=
  Quotient.lift (fun g => detU p g) (by
    intro a b hab
    obtain ⟨u, rfl⟩ := (fullRel_iff p h2 xs ys hxy a b).mp hab
    simp [map_mul, detU_unitRed p h2 xs ys hxy])

theorem fullDet_mk (g : MatrixUnits p) :
    fullDet p h2 xs ys hxy (Quotient.mk _ g) = detU p g := rfl

noncomputable def project : FullLevel p h2 xs ys hxy → SectionA3b.Yp p h2 xs ys hxy :=
  Quotient.lift (fun g => (Quotient.mk _ (projectivize p g) : SectionA3b.Yp p h2 xs ys hxy)) (by
    intro a b hab
    obtain ⟨u, rfl⟩ := (fullRel_iff p h2 xs ys hxy a b).mp hab
    apply Quotient.sound
    rw [QuotientGroup.rightRel_apply]
    refine ⟨u, ?_⟩
    change SectionA3a2.rho p h2 xs ys hxy u =
      projectivize p (unitRed p h2 xs ys hxy u * a) * (projectivize p a)⁻¹
    rw [map_mul]; group
    exact (projectivize_unitRed p h2 xs ys hxy u).symm)  -- UNTESTED: `group` may close/alter the goal

theorem project_mk (g : MatrixUnits p) :
    project p h2 xs ys hxy (Quotient.mk _ g) = Quotient.mk _ (projectivize p g) := rfl

theorem project_surjective : Function.Surjective (project p h2 xs ys hxy) := by
  intro y
  induction y using Quotient.inductionOn with
  | h g0 =>
    obtain ⟨g, rfl⟩ := projectivize_surjective p g0
    exact ⟨Quotient.mk _ g, rfl⟩

/-- χ on the projection is the Legendre symbol of the full-level determinant.  [SRC: chiP_mk, chiGL_val] -/
theorem chiY_project (s : FullLevel p h2 xs ys hxy) :
    chiY p h2 xs ys hxy (project p h2 xs ys hxy s) =
      ((quadraticChar (ZMod p) ((fullDet p h2 xs ys hxy s : (ZMod p)ˣ) : ZMod p) : ℤ) : ℂ) := by
  induction s using Quotient.inductionOn with
  | h g =>
    rw [project_mk, chiY_mk]
    change ((((chiP p (QuotientGroup.mk g)) : ℤˣ) : ℤ) : ℂ) = _
    rw [chiP_mk, chiGL_val, fullDet_mk, detU_val]

/-! ### 3. Determinant-fibre equivalence  [HAND: det fibre bijection] -/

theorem scalarUnit_central (c : (ZMod p)ˣ) :
    ∃ z : MatrixUnits p, z ∈ Subgroup.center (MatrixUnits p) ∧
      (z : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) (c : ZMod p) := by
  -- UNTESTED: construct the unit `scalar c` with inverse `scalar c⁻¹`, then use
  -- `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar` (used in StageA4o.chiGL_center).
  sorry  -- [GAP] elementary; to be filled against Mathlib names (Units.map of Matrix.scalar)

theorem det_scalar (c : ZMod p) :
    Matrix.det (Matrix.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) (ZMod p)) = c ^ 2 := by
  simp [Matrix.scalar_apply, Matrix.det_diagonal, sq]   -- copied from StageA4o.chiGL_center

/-- Injectivity on a determinant fibre: two full-level classes with the same determinant and the same
projective image coincide.  Hand proof: h = g'g⁻¹ = unitRed u · z, z central, det z = 1 ⇒ z = ±1 ∈ U. -/
theorem project_injOn_fibre (s t : FullLevel p h2 xs ys hxy)
    (hd : fullDet p h2 xs ys hxy s = fullDet p h2 xs ys hxy t)
    (hp : project p h2 xs ys hxy s = project p h2 xs ys hxy t) : s = t := by
  induction s using Quotient.inductionOn with
  | h g =>
  induction t using Quotient.inductionOn with
  | h g' =>
    -- from hp: ∃ u, rho u = proj g' * (proj g)⁻¹, so z := (unitRed u)⁻¹ * (g' * g⁻¹) is central
    -- from hd: det z = 1, so z = scalar r with r^2 = 1, r = ±1, hence z ∈ {1, unitRed negOne}
    -- and g' = unitRed (u or u * negOne) * g.
    sorry  -- [GAP] hand proof complete (see ScalarDescent-notes); Lean text not yet written

theorem project_surj_fibre (a : (ZMod p)ˣ) (y : SectionA3b.Yp p h2 xs ys hxy)
    (hy : chiY p h2 xs ys hxy y = ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ℂ)) :
    ∃ s : FullLevel p h2 xs ys hxy, fullDet p h2 xs ys hxy s = a ∧ project p h2 xs ys hxy s = y := by
  -- pick any lift G (project_surjective), b := det G, χ(b)=χ(a) from hy and chiY_project,
  -- a/b is a square c^2 (quadraticChar_one_iff_isSquare), take s := class of scalar(c) * G.
  sorry  -- [GAP] hand proof complete; uses scalarUnit_central, det_scalar

/-- Determinant fibre ≃ quadratic-character class. -/
noncomputable def detFibreEquiv (a : (ZMod p)ˣ) :
    {s : FullLevel p h2 xs ys hxy // fullDet p h2 xs ys hxy s = a} ≃
      {y : SectionA3b.Yp p h2 xs ys hxy //
        chiY p h2 xs ys hxy y = ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ℂ)} :=
  Equiv.ofBijective
    (fun s => ⟨project p h2 xs ys hxy s.1, by rw [chiY_project, s.2]⟩)
    ⟨fun s t hst => by
        apply Subtype.ext
        exact project_injOn_fibre p h2 xs ys hxy s.1 t.1 (s.2.trans t.2.symm) (congrArg Subtype.val hst),
     fun y => by
        obtain ⟨s, hs, hsy⟩ := project_surj_fibre p h2 xs ys hxy a y.1 y.2
        exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩⟩

/-! ### 4. Pullback and Weil-kernel membership -/

variable [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

/-- Unnormalised pullback `f ↦ f ∘ project` (no √|D| factor needed). -/
def pullback (f : EY p h2 xs ys hxy) : FullLevel p h2 xs ys hxy → ℂ :=
  fun s => f.ofLp (project p h2 xs ys hxy s)

theorem pullback_ne_zero (f : EY p h2 xs ys hxy) (hf : f ≠ 0) :
    pullback p h2 xs ys hxy f ≠ 0 := by
  intro h
  apply hf
  ext y
  obtain ⟨s, rfl⟩ := project_surjective p h2 xs ys hxy y
  simpa [pullback] using congrFun h s

open Classical in
theorem pullback_fibre_sum (f : EY p h2 xs ys hxy) (a : (ZMod p)ˣ) :
    (∑ s ∈ Finset.univ.filter (fun s => fullDet p h2 xs ys hxy s = a), pullback p h2 xs ys hxy f s) =
      ∑ y ∈ Finset.univ.filter (fun y =>
          chiY p h2 xs ys hxy y = ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ℂ)), f.ofLp y := by
  refine Finset.sum_bij (fun s _ => project p h2 xs ys hxy s) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rw [chiY_project, hs]
  · intro s hs t ht hst
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    exact project_injOn_fibre p h2 xs ys hxy s t (hs.trans ht.symm) hst
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨s, hs, hsy⟩ := project_surj_fibre p h2 xs ys hxy a y hy
    exact ⟨s, by simpa using hs, hsy⟩
  · intro s _; rfl

open Classical in
theorem pullback_mem_weilKernel (f : EY p h2 xs ys hxy)
    (h1 : inner ℂ (oneY p h2 xs ys hxy) f = 0) (hχ : inner ℂ (chiE p h2 xs ys hxy) f = 0) :
    pullback p h2 xs ys hxy f ∈
      LinearMap.ker (EulerWeilFibre.fibrePush (fullDet p h2 xs ys hxy)) := by
  rw [EulerWeilFibre.mem_ker_fibrePush]
  intro a
  rw [pullback_fibre_sum]
  obtain ⟨hp, hn⟩ := (EDc6.orth_iff_fibre_sums p h2 xs ys hxy f).mp ⟨h1, hχ⟩
  rcases quadraticChar_dichotomy (a.ne_zero) with h | h   -- UNTESTED name/arguments
  · simpa [h] using hp
  · simpa [h] using hn

/-! ### 5. Full-level Hecke operator (independent of the projective one) -/

/-- Shell element reduced to a matrix unit (needs `p ∤ n`). -/
noncomputable def shellUnit (n : ℕ) (hpn : ¬ p ∣ n) (x : Quaternion ℚ) (hx : x ∈ Section75a.Hn n) :
    MatrixUnits p :=
  SectionA2.redUnit p h2 xs ys hxy hx.1 n hx.2 hpn

open Classical in
/-- Full-level Hecke sum at a chosen representative `g` (full norm shell, divided by 24). -/
noncomputable def fullHeckeAt (n : ℕ) (hpn : ¬ p ∣ n) (F : FullLevel p h2 xs ys hxy → ℂ)
    (g : MatrixUnits p) : ℂ :=
  (∑ x ∈ (Section77a.Hn_finite n).toFinset.attach,
      F (Quotient.mk _ (shellUnit p h2 xs ys hxy n hpn x.1
        ((Set.Finite.mem_toFinset _).1 x.2) * g))) / 24

/-- [GAP] Representative independence.  Hand proof: if g' = unitRed u * g then
  shellUnit x * unitRed u = shellUnit (x*u) (red_mul), and x ↦ x*u permutes the full norm shell
  (Hn closed under right multiplication by Hurwitz units, inverse u⁻¹), so the sums agree.
  NOTE the RIGHT multiplication of the shell: the left action by units would be the wrong permutation. -/
theorem fullHeckeAt_respects (n : ℕ) (hpn : ¬ p ∣ n) (F : FullLevel p h2 xs ys hxy → ℂ)
    (a b : MatrixUnits p)
    (hab : QuotientGroup.rightRel (unitRedHom p h2 xs ys hxy).range a b) :
    fullHeckeAt p h2 xs ys hxy n hpn F a = fullHeckeAt p h2 xs ys hxy n hpn F b := by
  sorry  -- [GAP]

noncomputable def fullHecke (n : ℕ) (hpn : ¬ p ∣ n) (F : FullLevel p h2 xs ys hxy → ℂ) :
    FullLevel p h2 xs ys hxy → ℂ :=
  Quotient.lift (fun g => fullHeckeAt p h2 xs ys hxy n hpn F g)
    (fun a b hab => fullHeckeAt_respects p h2 xs ys hxy n hpn F a b hab)

/-- [GAP] Intertwining with the projective operator: `fullHecke (f ∘ project) = (Tl f) ∘ project`.
  Hand proof: π([red x · g]) = [rhoT x · projectivize g] (rhoT_of_unit, projectivize is a hom); then compare
  with `U_mk` (sum over `(Hn_finite n).toFinset`, convert `Finset.attach` sum by `Finset.sum_attach`) and
  `Tl_apply`/`Tn = U/24`.  No symmetry of the full-level operator is used. -/
theorem fullHecke_pullback (n : ℕ) (h : Adm p n) (f : EY p h2 xs ys hxy) :
    fullHecke p h2 xs ys hxy n h.2 (pullback p h2 xs ys hxy f) =
      pullback p h2 xs ys hxy (Tl p h2 xs ys hxy n f) := by
  sorry  -- [GAP]

/-! ### 6. CONDITIONAL transport (not the spectral theorem) -/

/-- The EXTERNAL obligation, stated on the actual full-level operator and actual Weil kernel.
It is a hypothesis, never proved here. -/
def FullLevelBound : Prop :=
  ∀ (l : ℕ) (hA : Adm p l), l.Prime → l % 4 = 3 →
    ∀ (μ : ℝ) (F : FullLevel p h2 xs ys hxy → ℂ), F ≠ 0 →
      F ∈ LinearMap.ker (EulerWeilFibre.fibrePush (fullDet p h2 xs ys hxy)) →
      fullHecke p h2 xs ys hxy l hA.2 F = (μ : ℂ) • F →
      |μ| ≤ 2 * Real.sqrt l

open Classical in
/-- CONDITIONAL finite transport: the full-level bound gives `RPEigenAt` at this splitting.
Uses: pullback ≠ 0 (surjectivity of `project`), Weil-kernel membership, intertwining [GAP: fullHecke_pullback]. -/
theorem rpeigenAt_of_fullLevel (hB : FullLevelBound p h2 xs ys hxy) :
    EDcSplitTransport.RPEigenAt p h2 xs ys hxy := by
  intro l hl hl4 hA μ f hf h1 hχ hT
  refine hB l hA hl hl4 μ (pullback p h2 xs ys hxy f) (pullback_ne_zero p h2 xs ys hxy f hf)
    (pullback_mem_weilKernel p h2 xs ys hxy f h1 hχ) ?_
  rw [fullHecke_pullback p h2 xs ys hxy l hA f, hT]
  ext s
  simp [pullback]

end EulerScalarDescent

#print axioms EulerScalarDescent.unitRedHom
#print axioms EulerScalarDescent.fullDet
#print axioms EulerScalarDescent.project_surjective
#print axioms EulerScalarDescent.chiY_project
#print axioms EulerScalarDescent.pullback_fibre_sum
#print axioms EulerScalarDescent.pullback_mem_weilKernel
#print axioms EulerScalarDescent.rpeigenAt_of_fullLevel
