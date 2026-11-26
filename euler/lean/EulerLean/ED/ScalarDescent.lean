import EDc10
import VertexDoubleOrbit
import FibrePushforward
import EDc8
import EDc9

/-!
# ScalarDescent.lean   — CI run 3 compiled the earlier draft (5 sorry GAPs); proofs added after that are UNTESTED until the next CI run

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

/-- `unitRed (-1) = -1` as a matrix unit.  [SRC: SectionA3a.red_negone in StageA4o.lean] -/
theorem unitRed_negOne :
    unitRed p h2 xs ys hxy SectionA3a2.negOne = (-1 : MatrixUnits p) := by
  apply Units.ext
  rw [unitRed_val]
  have : ((((SectionA3a2.negOne : SectionA3a2.HurU) : (Quaternion ℚ)ˣ)) : Quaternion ℚ) = -1 := rfl
  rw [this, SectionA3a.red_negone p h2 xs ys]
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
    refine QuotientGroup.rightRel_apply.mpr ⟨u, ?_⟩
    change SectionA3a2.rho p h2 xs ys hxy u =
      projectivize p (unitRed p h2 xs ys hxy u * a) * (projectivize p a)⁻¹
    rw [map_mul, mul_inv_cancel_right]
    exact (projectivize_unitRed p h2 xs ys hxy u).symm)

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
  refine ⟨Units.map (Matrix.scalar (Fin 2) :
      ZMod p →+* Matrix (Fin 2) (Fin 2) (ZMod p)).toMonoidHom c, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact ((Matrix.scalar_commute (n := Fin 2) (c : ZMod p) (fun r => Commute.all _ _)
    (g : Matrix (Fin 2) (Fin 2) (ZMod p))).eq).symm

theorem det_scalar (c : ZMod p) :
    Matrix.det (Matrix.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) (ZMod p)) = c ^ 2 := by
  simp [Matrix.scalar_apply, Matrix.det_diagonal, sq]   -- copied from StageA4o.chiGL_center

/-- A central unit of determinant 1 is 1 or the image of -1.  [UNTESTED until next CI run] -/
theorem central_det_one (z : MatrixUnits p) (hz : z ∈ Subgroup.center (MatrixUnits p))
    (hd : detU p z = 1) : z = 1 ∨ z = unitRed p h2 xs ys hxy SectionA3a2.negOne := by
  obtain ⟨r, hr⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).1 hz
  have h1 : r ^ 2 = 1 := by
    have h := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hd
    simp only at h
    rw [detU_val, ← hr, det_scalar] at h
    simpa using h
  have h3 : r = 1 ∨ r = -1 := by
    have h4 : (r - 1) * (r + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases h3 with rfl | rfl
  · left
    apply Units.ext
    rw [← hr]
    simp
  · right
    rw [unitRed_negOne]
    apply Units.ext
    rw [← hr]
    simp

/-- Injectivity on a determinant fibre: two full-level classes with the same determinant and the same
projective image coincide.  Hand proof: h = g'g⁻¹ = unitRed u · z, z central, det z = 1 ⇒ z = ±1 ∈ U. -/
theorem project_injOn_fibre (s t : FullLevel p h2 xs ys hxy)
    (hd : fullDet p h2 xs ys hxy s = fullDet p h2 xs ys hxy t)
    (hp : project p h2 xs ys hxy s = project p h2 xs ys hxy t) : s = t := by
  induction s using Quotient.inductionOn with
  | h g =>
  induction t using Quotient.inductionOn with
  | h g' =>
    rw [project_mk, project_mk] at hp
    rw [fullDet_mk, fullDet_mk] at hd
    have hmem : projectivize p g' * (projectivize p g)⁻¹ ∈ SectionA3b.Gam p h2 xs ys hxy :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hp)
    obtain ⟨u, hu⟩ := hmem
    obtain ⟨z, hzdef⟩ : ∃ z : MatrixUnits p,
        z = (unitRed p h2 xs ys hxy u)⁻¹ * (g' * g⁻¹) := ⟨_, rfl⟩
    have hπ : projectivize p z = 1 := by
      rw [hzdef]
      simp only [map_mul, map_inv, projectivize_unitRed]
      rw [hu]
      exact inv_mul_cancel _
    have hzc : z ∈ Subgroup.center (MatrixUnits p) := (QuotientGroup.eq_one_iff z).mp hπ
    have hz1 : detU p z = 1 := by
      rw [hzdef]
      simp only [map_mul, map_inv, detU_unitRed p h2 xs ys hxy, hd]
      simp
    have hrec : g' = unitRed p h2 xs ys hxy u * z * g := by
      rw [hzdef]; group
    apply Quotient.sound
    rcases central_det_one p h2 xs ys hxy z hzc hz1 with h | h
    · refine (fullRel_iff p h2 xs ys hxy g g').mpr ⟨u, ?_⟩
      rw [hrec, h]; group
    · refine (fullRel_iff p h2 xs ys hxy g g').mpr ⟨u * SectionA3a2.negOne, ?_⟩
      have e : unitRed p h2 xs ys hxy (u * SectionA3a2.negOne) =
          unitRed p h2 xs ys hxy u * unitRed p h2 xs ys hxy SectionA3a2.negOne :=
        (unitRedHom p h2 xs ys hxy).map_mul u SectionA3a2.negOne
      rw [e, hrec, h]; group

theorem project_surj_fibre (a : (ZMod p)ˣ) (y : SectionA3b.Yp p h2 xs ys hxy)
    (hy : chiY p h2 xs ys hxy y = ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ℂ)) :
    ∃ s : FullLevel p h2 xs ys hxy, fullDet p h2 xs ys hxy s = a ∧ project p h2 xs ys hxy s = y := by
  obtain ⟨s0, hs0⟩ := project_surjective p h2 xs ys hxy y
  obtain ⟨G, rfl⟩ := Quotient.exists_rep s0
  have hchi := chiY_project p h2 xs ys hxy (Quotient.mk _ G)
  rw [hs0, hy, fullDet_mk] at hchi
  have hqq : quadraticChar (ZMod p) (a : ZMod p) =
      quadraticChar (ZMod p) ((detU p G : (ZMod p)ˣ) : ZMod p) := by
    exact_mod_cast hchi
  have hbne : ((detU p G : (ZMod p)ˣ) : ZMod p) ≠ 0 := (detU p G).ne_zero
  have habne : (a : ZMod p) ≠ 0 := a.ne_zero
  have hone : quadraticChar (ZMod p) ((a : ZMod p) * ((detU p G : (ZMod p)ˣ) : ZMod p)) = 1 := by
    rw [quadraticChar_mul, hqq, ← quadraticChar_mul, ← sq, quadraticChar_sq_one' hbne]
  obtain ⟨c, hc⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero habne hbne)).mp hone
  have hc0 : c ≠ 0 := by
    intro h
    apply mul_ne_zero habne hbne
    rw [hc, h]; ring
  have hd0 : c * ((detU p G : (ZMod p)ˣ) : ZMod p)⁻¹ ≠ 0 := mul_ne_zero hc0 (inv_ne_zero hbne)
  obtain ⟨z, hzc, hzv⟩ := scalarUnit_central p (Units.mk0 _ hd0)
  rw [Units.val_mk0] at hzv
  have hπz : projectivize p z = 1 := (QuotientGroup.eq_one_iff z).mpr hzc
  have key : (a : ZMod p) = c * c * ((detU p G : (ZMod p)ˣ) : ZMod p)⁻¹ := by
    rw [← hc]; field_simp
  refine ⟨Quotient.mk _ (z * G), ?_, ?_⟩
  · rw [fullDet_mk]
    apply Units.ext
    rw [detU_val, Units.val_mul, Matrix.det_mul, hzv, det_scalar, ← detU_val, key]
    first | (field_simp; ring) | field_simp
  · rw [project_mk, map_mul, hπz, one_mul]
    rw [project_mk] at hs0
    exact hs0

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

-- (Fintype section variables removed: run #2 showed they were unused and could clash with EDc8's instances.)

/-- Unnormalised pullback `f ↦ f ∘ project` (no √|D| factor needed). -/
noncomputable def pullback (f : EY p h2 xs ys hxy) : FullLevel p h2 xs ys hxy → ℂ :=
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

theorem mem_Hn_mul_unit {n : ℕ} {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn n)
    (v : (Quaternion ℚ)ˣ) (hv : v ∈ SectionA3a2.HurU) :
    x * (v : Quaternion ℚ) ∈ Section75a.Hn n := by
  obtain ⟨hvq, hvn⟩ := (SectionA3a2.mem_iff v).mp hv
  exact ⟨Section71d.QH_mul hx.1 hvq, by rw [map_mul, hx.2, hvn, mul_one]⟩

theorem shellUnit_eq_mul (n : ℕ) (hpn : ¬ p ∣ n) {y z : Quaternion ℚ}
    (hy : y ∈ Section75a.Hn n) (hz : z ∈ Section75a.Hn n) (u : SectionA3a2.HurU)
    (h : z = y * (((u : (Quaternion ℚ)ˣ)) : Quaternion ℚ)) :
    shellUnit p h2 xs ys hxy n hpn z hz =
      shellUnit p h2 xs ys hxy n hpn y hy * unitRed p h2 xs ys hxy u := by
  subst h
  apply Units.ext
  rw [Units.val_mul]
  unfold shellUnit
  rw [SectionA2.redUnit_coe, SectionA2.redUnit_coe, unitRed_val,
    Section74b.red_mul p h2 xs ys hxy hy.1 ((SectionA3a2.mem_iff _).mp u.2).1]

/-- Representative independence (attempt, UNTESTED until CI).  If g' = unitRed u * g then
  shellUnit y * unitRed u = shellUnit (y*u) (red_mul), and x ↦ x*u permutes the full norm shell.
  NOTE the RIGHT multiplication of the shell. -/
theorem fullHeckeAt_respects (n : ℕ) (hpn : ¬ p ∣ n) (F : FullLevel p h2 xs ys hxy → ℂ)
    (a b : MatrixUnits p)
    (hab : QuotientGroup.rightRel (unitRedHom p h2 xs ys hxy).range a b) :
    fullHeckeAt p h2 xs ys hxy n hpn F a = fullHeckeAt p h2 xs ys hxy n hpn F b := by
  obtain ⟨u, rfl⟩ := (fullRel_iff p h2 xs ys hxy a b).mp hab
  unfold fullHeckeAt
  congr 1
  have hu : ((u : (Quaternion ℚ)ˣ)) ∈ SectionA3a2.HurU := u.2
  have hui : ((u : (Quaternion ℚ)ˣ))⁻¹ ∈ SectionA3a2.HurU := inv_mem hu
  refine Finset.sum_bij'
    (fun x _ => (⟨x.1 * ((((u : (Quaternion ℚ)ˣ))⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ),
        (Set.Finite.mem_toFinset _).2
          (mem_Hn_mul_unit ((Set.Finite.mem_toFinset _).1 x.2) _ hui)⟩ :
        {x // x ∈ (Section77a.Hn_finite n).toFinset}))
    (fun y _ => (⟨y.1 * (((u : (Quaternion ℚ)ˣ)) : Quaternion ℚ),
        (Set.Finite.mem_toFinset _).2
          (mem_Hn_mul_unit ((Set.Finite.mem_toFinset _).1 y.2) _ hu)⟩ :
        {x // x ∈ (Section77a.Hn_finite n).toFinset}))
    (fun _ _ => Finset.mem_attach _ _) (fun _ _ => Finset.mem_attach _ _) ?_ ?_ ?_
  · intro x _
    apply Subtype.ext
    show x.1 * ((((u : (Quaternion ℚ)ˣ))⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ) * (((u : (Quaternion ℚ)ˣ)) : Quaternion ℚ) = x.1
    rw [mul_assoc, Units.inv_mul, mul_one]
  · intro y _
    apply Subtype.ext
    show y.1 * (((u : (Quaternion ℚ)ˣ)) : Quaternion ℚ) * ((((u : (Quaternion ℚ)ˣ))⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ) = y.1
    rw [mul_assoc, Units.mul_inv, mul_one]
  · intro x _
    have hx := (Set.Finite.mem_toFinset _).1 x.2
    have hxi : x.1 * ((((u : (Quaternion ℚ)ˣ))⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ) ∈ Section75a.Hn n := mem_Hn_mul_unit hx _ hui
    have hrel : x.1 = (x.1 * ((((u : (Quaternion ℚ)ˣ))⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ)) * (((u : (Quaternion ℚ)ˣ)) : Quaternion ℚ) := by
      rw [mul_assoc, Units.inv_mul, mul_one]
    show F (Quotient.mk _ (shellUnit p h2 xs ys hxy n hpn x.1 hx * a)) =
      F (Quotient.mk _ (shellUnit p h2 xs ys hxy n hpn (x.1 * ((((u : (Quaternion ℚ)ˣ))⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ)) hxi *
          (unitRed p h2 xs ys hxy u * a)))
    rw [shellUnit_eq_mul p h2 xs ys hxy n hpn hxi hx u hrel, mul_assoc]

noncomputable def fullHecke (n : ℕ) (hpn : ¬ p ∣ n) (F : FullLevel p h2 xs ys hxy → ℂ) :
    FullLevel p h2 xs ys hxy → ℂ :=
  Quotient.lift (fun g => fullHeckeAt p h2 xs ys hxy n hpn F g)
    (fun a b hab => fullHeckeAt_respects p h2 xs ys hxy n hpn F a b hab)

theorem pi_shellUnit (n : ℕ) (hpn : ¬ p ∣ n) (x : Quaternion ℚ) (hx : x ∈ Section75a.Hn n) :
    projectivize p (shellUnit p h2 xs ys hxy n hpn x hx) = SectionA4e.rhoT p xs ys x := by
  have hu : IsUnit (Section74b.red p xs ys x) :=
    SectionA4e.isUnit_red_of_mem p h2 xs ys hxy hpn hx
  rw [SectionA4e.rhoT_of_unit p xs ys hu]
  show (QuotientGroup.mk (shellUnit p h2 xs ys hxy n hpn x hx) : SectionA2.PGL2 p) =
    QuotientGroup.mk hu.unit
  congr 1
  apply Units.ext
  rw [IsUnit.unit_spec]
  exact SectionA2.redUnit_coe p h2 xs ys hxy hx.1 n hx.2 hpn

/-- Intertwining with the projective operator (attempt, UNTESTED until CI):
  fullHecke (f ∘ project) = (Tl f) ∘ project.  No symmetry of the full-level operator is used. -/
theorem fullHecke_pullback (n : ℕ) (h : SectionA4l.Adm p n) (f : EY p h2 xs ys hxy) :
    fullHecke p h2 xs ys hxy n h.2 (pullback p h2 xs ys hxy f) =
      pullback p h2 xs ys hxy (Tl p h2 xs ys hxy n f) := by
  funext s
  induction s using Quotient.inductionOn with
  | h g =>
    have hL : fullHecke p h2 xs ys hxy n h.2 (pullback p h2 xs ys hxy f) (Quotient.mk _ g) =
        fullHeckeAt p h2 xs ys hxy n h.2 (pullback p h2 xs ys hxy f) g := rfl
    rw [hL]
    unfold fullHeckeAt
    have hR : pullback p h2 xs ys hxy (Tl p h2 xs ys hxy n f) (Quotient.mk _ g) =
        (SectionA4e.U p h2 xs ys hxy n h.2 f.ofLp
          (Quotient.mk _ (projectivize p g))) / 24 := by
      show (Tl p h2 xs ys hxy n f).ofLp (project p h2 xs ys hxy (Quotient.mk _ g)) = _
      rw [project_mk, Tl_apply p h2 xs ys hxy n h]
      rfl
    rw [hR, SectionA4e.U_mk]
    congr 1
    rw [← Finset.sum_attach ((Section77a.Hn_finite n).toFinset)
      (fun x => f.ofLp (Quotient.mk _ (SectionA4e.rhoT p xs ys x * projectivize p g)))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hx : x.1 ∈ Section75a.Hn n := (Set.Finite.mem_toFinset _).1 x.2
    show f.ofLp (project p h2 xs ys hxy
      (Quotient.mk _ (shellUnit p h2 xs ys hxy n h.2 x.1 hx * g))) = _
    rw [project_mk, map_mul, pi_shellUnit p h2 xs ys hxy n h.2 x.1 hx]

/-! ### 6. CONDITIONAL transport (not the spectral theorem) -/

/-- The EXTERNAL obligation, stated on the actual full-level operator and actual Weil kernel.
It is a hypothesis, never proved here. -/
def FullLevelBound : Prop :=
  ∀ (l : ℕ) (hA : SectionA4l.Adm p l), l.Prime → l % 4 = 3 →
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
