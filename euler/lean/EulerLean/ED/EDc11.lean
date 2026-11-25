import StageA4o

/-!
# edge_count.lean   (UNTESTED: not compiled anywhere; CI is the only compiler)

Bridge 3, finite algebra only.  Label of every result below: *finite bookkeeping* (no use of `RPEigen`, no external
mathematics).  `RPEigen` is OPEN and is neither used nor asserted here.

## Hand derivation
Fix `p`, a splitting `(xs, ys)`, `l` with `p ∤ l`, and `g h : PGL₂(F_p)`.  Write `Γ = Gam`, `Hn l` = Hurwitz quaternions of
norm `l`, and
  `NEnd g h  = {α ∈ Hn l | rhoT α * g = h}`          (so `N_ij = #NEnd g_i g_j`),
  `NCos g h  = {α ∈ Hn l | ∃ γ ∈ Γ, rhoT α * g = γ * h}`.
(1) `#NCos g h = 12 * #NEnd g h`.  Every `γ ∈ Γ` is `rho u` with `u ∈ HurU` (Nrd u = 1); choose `uOf γ`.  The map
    `(γ, α') ↦ qv(uOf γ) * α'` is a bijection `Γ × NEnd g h → NCos g h` with inverse `α ↦ (γ, qv(uOf γ)⁻¹ * α)`:
    norm is preserved since `Nrd u = 1`, `rhoT (u α') = rho u * rhoT α'` by `rhoT_mul`, and `γ` is unique because
    `γ * h = γ' * h → γ = γ'` (right cancellation, `free_left`-style).  `#Γ = 12` is `card_Gam`.
(2) `N_ij = N_ji` by `α ↦ star α` (`rhoT (star α) = (rhoT α)⁻¹`, from `aH_star` and `rhoT_aH`), applied to the exact
    endpoints `rep i, rep j` (this is the exact-endpoint symmetry of handoff/EndpointSymmetry.lean, stated for `rhoT`).
(3) Matrix form: for `f : Y_p → ℂ`, with `rep := Quotient.out`, `U_l f (i) = Σ_{x ∈ Hn l} f [rhoT x * rep i]
    = Σ_j #{x | [rhoT x * rep i] = j} f j = Σ_j 12 N_ij f j` (fibre decomposition + (1) + `mk_eq_iff`), hence
    `T_l f (i) = U_l f(i)/24 = Σ_j (N_ij / 2) f j`.  Entries `N_ij/2` are rational, hence real; symmetric by (2).

## Names checked by grep in StageA4o.lean (compiled source of truth)
SectionA3b.{Gam, card_Gam, Yp}; SectionA3a2.{HurU, rho, mem_iff}; SectionA3a3.{qv, qv_QH, qv_norm};
SectionA4b.{Hm, aH, starEquiv, aH_star}; SectionA4e.{rhoT, rhoT_of_unit, rhoT_aH, rhoT_mul, U, U_mk};
SectionA4g.Tn (= U/24); SectionA4a.mk_eq_of_eq_mul; SectionA1.red_isUnit; SectionA3a.not_dvd_one_p;
Section75a.Hn; Section77a.Hn_finite; Section73a.{QH_star, normSq_star'}; Section71d.{QH, QH_mul}.
## Mathlib names NOT checked (no toolchain): Nat.card_prod, Nat.card_congr, Equiv.ofBijective, Equiv.subtypeEquivRight,
Finset.sum_fiberwise (argument form and filter notation may differ), Set.Finite.mem_toFinset, MonoidHom.mem_range,
Quotient.exact, Quotient.out_eq, QuotientGroup.rightRel_apply, Subgroup.coe_inv/coe_one simp lemmas.

## What this establishes (if it compiles)
Counting identity (1), symmetry (2), matrix identity (3) for `T_l = Tn`, all for exact finite data.
## What it does NOT establish
No identification of `Y_p` with supersingular curves or of `N_ij` with isogeny counts (Deuring / Brandt, external),
nothing about eigenvalues, `RPEigen`, Ramanujan bounds, or Codogni-Lido.  Independence of `N_ij` from the choice of
representatives is not claimed (the matrix is defined with `Quotient.out`).
-/

namespace EdgeCount
open Section71d SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- exact endpoints: Hurwitz quaternions of norm `l` taking `g` to `h` -/
def NEnd (l : ℕ) (g h : SectionA2.PGL2 p) : Type :=
  {α : Quaternion ℚ // α ∈ Section75a.Hn l ∧ rhoT p xs ys α * g = h}

/-- Hurwitz quaternions of norm `l` taking `g` into the coset `Γ h` -/
def NCos (l : ℕ) (g h : SectionA2.PGL2 p) : Type :=
  {α : Quaternion ℚ // α ∈ Section75a.Hn l ∧
    ∃ γ ∈ SectionA3b.Gam p h2 xs ys hxy, rhoT p xs ys α * g = γ * h}

theorem rhoT_rho (u : SectionA3a2.HurU) :
    rhoT p xs ys (SectionA3a3.qv u) = SectionA3a2.rho p h2 xs ys hxy u := by
  have hu : IsUnit (Section74b.red p xs ys (SectionA3a3.qv u)) :=
    SectionA1.red_isUnit p h2 xs ys hxy (SectionA3a3.qv_QH u) 1
      (by rw [SectionA3a3.qv_norm]; norm_num) (SectionA3a.not_dvd_one_p p)
  rw [rhoT_of_unit p xs ys hu]
  rfl

theorem leftAct (u : SectionA3a2.HurU) (l : ℕ) (hpl : ¬ p ∣ l) {α : Quaternion ℚ}
    (hα : α ∈ Section75a.Hn l) :
    SectionA3a3.qv u * α ∈ Section75a.Hn l ∧
      rhoT p xs ys (SectionA3a3.qv u * α) = SectionA3a2.rho p h2 xs ys hxy u * rhoT p xs ys α := by
  have hαu : IsUnit (Section74b.red p xs ys α) :=
    SectionA1.red_isUnit p h2 xs ys hxy hα.1 l hα.2 hpl
  have hu : IsUnit (Section74b.red p xs ys (SectionA3a3.qv u)) :=
    SectionA1.red_isUnit p h2 xs ys hxy (SectionA3a3.qv_QH u) 1
      (by rw [SectionA3a3.qv_norm]; norm_num) (SectionA3a.not_dvd_one_p p)
  refine ⟨⟨QH_mul (SectionA3a3.qv_QH u) hα.1, ?_⟩, ?_⟩
  · rw [map_mul, SectionA3a3.qv_norm, one_mul]; exact hα.2
  · rw [rhoT_mul p h2 xs ys hxy (SectionA3a3.qv_QH u) hα.1 hu hαu, rhoT_rho p h2 xs ys hxy]

theorem qv_inv_mul (u : SectionA3a2.HurU) (x : Quaternion ℚ) :
    SectionA3a3.qv u⁻¹ * (SectionA3a3.qv u * x) = x := by
  calc SectionA3a3.qv u⁻¹ * (SectionA3a3.qv u * x)
      = (SectionA3a3.qv u⁻¹ * SectionA3a3.qv u) * x := (mul_assoc _ _ _).symm
    _ = SectionA3a3.qv (u⁻¹ * u) * x := rfl
    _ = x := by rw [inv_mul_cancel]; simp [SectionA3a3.qv]

theorem qv_mul_inv (u : SectionA3a2.HurU) (x : Quaternion ℚ) :
    SectionA3a3.qv u * (SectionA3a3.qv u⁻¹ * x) = x := by
  calc SectionA3a3.qv u * (SectionA3a3.qv u⁻¹ * x)
      = (SectionA3a3.qv u * SectionA3a3.qv u⁻¹) * x := (mul_assoc _ _ _).symm
    _ = SectionA3a3.qv (u * u⁻¹) * x := rfl
    _ = x := by rw [mul_inv_cancel]; simp [SectionA3a3.qv]

theorem mem_Gam (γ : SectionA2.PGL2 p) :
    γ ∈ SectionA3b.Gam p h2 xs ys hxy ↔ ∃ u : SectionA3a2.HurU, SectionA3a2.rho p h2 xs ys hxy u = γ := by
  unfold SectionA3b.Gam
  exact MonoidHom.mem_range

/-- a Hurwitz unit representing `γ ∈ Γ` -/
noncomputable def uOf (γ : SectionA3b.Gam p h2 xs ys hxy) : SectionA3a2.HurU :=
  Classical.choose ((mem_Gam p h2 xs ys hxy γ.1).1 γ.2)

theorem uOf_spec (γ : SectionA3b.Gam p h2 xs ys hxy) :
    SectionA3a2.rho p h2 xs ys hxy (uOf p h2 xs ys hxy γ) = γ.1 :=
  Classical.choose_spec ((mem_Gam p h2 xs ys hxy γ.1).1 γ.2)

/-- the map `(γ, α') ↦ qv(uOf γ) * α'` -/
noncomputable def cosMap (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p) :
    SectionA3b.Gam p h2 xs ys hxy × NEnd p xs ys l g h → NCos p h2 xs ys hxy l g h :=
  fun x =>
    ⟨SectionA3a3.qv (uOf p h2 xs ys hxy x.1) * x.2.1,
      (leftAct p h2 xs ys hxy _ l hpl x.2.2.1).1,
      x.1.1, x.1.2, by
        rw [(leftAct p h2 xs ys hxy _ l hpl x.2.2.1).2, uOf_spec p h2 xs ys hxy, mul_assoc, x.2.2.2]⟩

theorem cosMap_injective (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p) :
    Function.Injective (cosMap p h2 xs ys hxy l hpl g h) := by
  rintro ⟨γ, α, hα, hr⟩ ⟨γ', α', hα', hr'⟩ hEq
  have hv : SectionA3a3.qv (uOf p h2 xs ys hxy γ) * α = SectionA3a3.qv (uOf p h2 xs ys hxy γ') * α' :=
    congrArg Subtype.val hEq
  -- rhoT of the common image, computed two ways
  have e1 := (leftAct p h2 xs ys hxy (uOf p h2 xs ys hxy γ) l hpl hα).2
  have e2 := (leftAct p h2 xs ys hxy (uOf p h2 xs ys hxy γ') l hpl hα').2
  rw [hv] at e1
  rw [e1, uOf_spec, uOf_spec] at e2
  -- e2 : γ.1 * rhoT α = γ'.1 * rhoT α'  (after rewriting); recover γ = γ' from the endpoint
  have hγ : γ.1 = γ'.1 := by
    have h3 : γ.1 * rhoT p xs ys α * g = γ'.1 * rhoT p xs ys α' * g := by rw [e2]
    rw [mul_assoc, hr, mul_assoc, hr'] at h3
    exact mul_right_cancel h3
  have hγ' : γ = γ' := Subtype.ext hγ
  subst hγ'
  have h3 : SectionA3a3.qv (uOf p h2 xs ys hxy γ)⁻¹ * (SectionA3a3.qv (uOf p h2 xs ys hxy γ) * α)
      = SectionA3a3.qv (uOf p h2 xs ys hxy γ)⁻¹ * (SectionA3a3.qv (uOf p h2 xs ys hxy γ) * α') := by
    rw [hv]
  rw [qv_inv_mul, qv_inv_mul] at h3
  subst h3
  rfl

theorem cosMap_surjective (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p) :
    Function.Surjective (cosMap p h2 xs ys hxy l hpl g h) := by
  rintro ⟨α, hα, γ, hγ, hr⟩
  set γ' : SectionA3b.Gam p h2 xs ys hxy := ⟨γ, hγ⟩ with hγ'
  set u := uOf p h2 xs ys hxy γ' with hu
  have hl := leftAct p h2 xs ys hxy u⁻¹ l hpl hα
  have hspec : SectionA3a2.rho p h2 xs ys hxy u = γ := uOf_spec p h2 xs ys hxy γ'
  refine ⟨(γ', ⟨SectionA3a3.qv u⁻¹ * α, hl.1, ?_⟩), ?_⟩
  · rw [hl.2, map_inv, hspec, mul_assoc, hr, inv_mul_cancel_left]
  · apply Subtype.ext
    show SectionA3a3.qv (uOf p h2 xs ys hxy γ') * (SectionA3a3.qv u⁻¹ * α) = α
    rw [← hu]
    exact qv_mul_inv u α

/-- (1) the coset count is `12` times the exact count (bijection `α ↦ u⁻¹ α`, `Nrd u = 1`).
FINITE BOOKKEEPING; does not use `RPEigen`. -/
theorem card_cos_eq (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p) :
    Nat.card (NCos p h2 xs ys hxy l g h) = 12 * Nat.card (NEnd p xs ys l g h) := by
  calc Nat.card (NCos p h2 xs ys hxy l g h)
      = Nat.card (SectionA3b.Gam p h2 xs ys hxy × NEnd p xs ys l g h) :=
        (Nat.card_congr (Equiv.ofBijective _
          ⟨cosMap_injective p h2 xs ys hxy l hpl g h, cosMap_surjective p h2 xs ys hxy l hpl g h⟩)).symm
    _ = Nat.card (SectionA3b.Gam p h2 xs ys hxy) * Nat.card (NEnd p xs ys l g h) := Nat.card_prod _ _
    _ = 12 * Nat.card (NEnd p xs ys l g h) := by rw [SectionA3b.card_Gam p h2 xs ys hxy]

/-! ### (2) symmetry -/

theorem star_mem_Hn (l : ℕ) {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn l) : star x ∈ Section75a.Hn l :=
  ⟨Section73a.QH_star hx.1, by rw [Section73a.normSq_star']; exact hx.2⟩

include h2 hxy in
theorem rhoT_star (l : ℕ) (hpl : ¬ p ∣ l) {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn l) :
    rhoT p xs ys (star x) = (rhoT p xs ys x)⁻¹ := by
  have e1 := rhoT_aH p h2 xs ys hxy l hpl (⟨x, hx.1, hx.2⟩ : SectionA4b.Hm l)
  have e2 := rhoT_aH p h2 xs ys hxy l hpl (SectionA4b.starEquiv l (⟨x, hx.1, hx.2⟩ : SectionA4b.Hm l))
  have e3 := SectionA4b.aH_star p h2 xs ys hxy l hpl (⟨x, hx.1, hx.2⟩ : SectionA4b.Hm l)
  calc rhoT p xs ys (star x)
      = rhoT p xs ys (SectionA4b.starEquiv l (⟨x, hx.1, hx.2⟩ : SectionA4b.Hm l)).1 := rfl
    _ = SectionA4b.aH p h2 xs ys hxy l hpl (SectionA4b.starEquiv l (⟨x, hx.1, hx.2⟩ : SectionA4b.Hm l)) := e2
    _ = (SectionA4b.aH p h2 xs ys hxy l hpl (⟨x, hx.1, hx.2⟩ : SectionA4b.Hm l))⁻¹ := e3
    _ = (rhoT p xs ys x)⁻¹ := by rw [← e1]

/-- exact endpoints are reversed by quaternion conjugation -/
noncomputable def endEquiv (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p) :
    NEnd p xs ys l g h ≃ NEnd p xs ys l h g where
  toFun α := ⟨star α.1, star_mem_Hn l α.2.1, by
    rw [rhoT_star p h2 xs ys hxy l hpl α.2.1]
    have hrev := congrArg (fun z : SectionA2.PGL2 p => (rhoT p xs ys α.1)⁻¹ * z) α.2.2
    simpa only [inv_mul_cancel_left] using hrev.symm⟩
  invFun α := ⟨star α.1, star_mem_Hn l α.2.1, by
    rw [rhoT_star p h2 xs ys hxy l hpl α.2.1]
    have hrev := congrArg (fun z : SectionA2.PGL2 p => (rhoT p xs ys α.1)⁻¹ * z) α.2.2
    simpa only [inv_mul_cancel_left] using hrev.symm⟩
  left_inv α := Subtype.ext (star_star α.1)
  right_inv α := Subtype.ext (star_star α.1)

include h2 hxy in
/-- (2) `N_ij = N_ji` for exact endpoints.  FINITE BOOKKEEPING. -/
theorem card_end_symm (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p) :
    Nat.card (NEnd p xs ys l g h) = Nat.card (NEnd p xs ys l h g) :=
  Nat.card_congr (endEquiv p h2 xs ys hxy l hpl g h)

/-! ### (3) matrix form of `T_l = U_l / 24` -/

abbrev Y : Type := SectionA3b.Yp p h2 xs ys hxy

/-- chosen representative of a class -/
noncomputable def rep (y : Y p h2 xs ys hxy) : SectionA2.PGL2 p := Quotient.out y

theorem mk_rep (y : Y p h2 xs ys hxy) :
    Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) (rep p h2 xs ys hxy y) = y :=
  Quotient.out_eq y

theorem mk_eq_iff (a b : SectionA2.PGL2 p) :
    Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) a
        = Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) b
      ↔ ∃ γ ∈ SectionA3b.Gam p h2 xs ys hxy, a = γ * b := by
  constructor
  · intro h
    have h' := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
    exact ⟨(b * a⁻¹)⁻¹, (SectionA3b.Gam p h2 xs ys hxy).inv_mem h', by group⟩
  · rintro ⟨γ, hγ, e⟩
    exact SectionA4a.mk_eq_of_eq_mul _ γ hγ e

/-- the exact-endpoint count matrix `N_ij` (with `Quotient.out` representatives) -/
noncomputable def Nmat (l : ℕ) (i j : Y p h2 xs ys hxy) : ℕ :=
  Nat.card (NEnd p xs ys l (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j))

/-- the Hecke matrix `(T_l)_ij = N_ij / 2` (rational, hence real) -/
noncomputable def Tmat (l : ℕ) (i j : Y p h2 xs ys hxy) : ℚ :=
  (Nmat p h2 xs ys hxy l i j : ℚ) / 2

/-- symmetry of the matrix.  FINITE BOOKKEEPING. -/
theorem Tmat_symm (l : ℕ) (hpl : ¬ p ∣ l) (i j : Y p h2 xs ys hxy) :
    Tmat p h2 xs ys hxy l i j = Tmat p h2 xs ys hxy l j i := by
  unfold Tmat Nmat
  have h := card_end_symm p h2 xs ys hxy l hpl (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j)
  have h' : ((Nat.card (NEnd p xs ys l (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j)) : ℕ) : ℚ)
      = ((Nat.card (NEnd p xs ys l (rep p h2 xs ys hxy j) (rep p h2 xs ys hxy i)) : ℕ) : ℚ) := by
    exact_mod_cast h
  rw [h']

theorem natCard_eq_filter (l : ℕ) (P : Quaternion ℚ → Prop) [DecidablePred P] :
    Nat.card {α : Quaternion ℚ // α ∈ Section75a.Hn l ∧ P α}
      = ((Section77a.Hn_finite l).toFinset.filter P).card := by
  classical
  have e : {α : Quaternion ℚ // α ∈ Section75a.Hn l ∧ P α}
      ≃ {x : Quaternion ℚ // x ∈ (Section77a.Hn_finite l).toFinset.filter P} :=
    Equiv.subtypeEquivRight (fun x => by simp [Finset.mem_filter, Set.Finite.mem_toFinset])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- (3) `U_l f (i) = Σ_j 12 N_ij f(j)`.  FINITE BOOKKEEPING (needs `Fintype Y_p`, as assumed). -/
theorem U_matrix [Fintype (Y p h2 xs ys hxy)] (l : ℕ) (hpl : ¬ p ∣ l)
    (f : Y p h2 xs ys hxy → ℂ) (i : Y p h2 xs ys hxy) :
    U p h2 xs ys hxy l hpl f i
      = ∑ j, ((12 * Nmat p h2 xs ys hxy l i j : ℕ) : ℂ) * f j := by
  classical
  have h0 := U_mk p h2 xs ys hxy l hpl f (rep p h2 xs ys hxy i)
  rw [mk_rep p h2 xs ys hxy i] at h0
  rw [h0]
  rw [← Finset.sum_fiberwise (Section77a.Hn_finite l).toFinset
    (fun x => Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
      (rhoT p xs ys x * rep p h2 xs ys hxy i))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hc : ∀ x ∈ (Section77a.Hn_finite l).toFinset.filter (fun x =>
      Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (rhoT p xs ys x * rep p h2 xs ys hxy i) = j),
      f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (rhoT p xs ys x * rep p h2 xs ys hxy i)) = f j :=
    fun x hx => by rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Section77a.Hn_finite l).toFinset.filter (fun x =>
      Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (rhoT p xs ys x * rep p h2 xs ys hxy i) = j)).card
      = 12 * Nmat p h2 xs ys hxy l i j := by
    rw [← natCard_eq_filter l]
    have e : {α : Quaternion ℚ // α ∈ Section75a.Hn l ∧
          Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
            (rhoT p xs ys α * rep p h2 xs ys hxy i) = j}
        ≃ NCos p h2 xs ys hxy l (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j) :=
      Equiv.subtypeEquivRight (fun α => and_congr_right (fun _ => by
        have := mk_eq_iff p h2 xs ys hxy (rhoT p xs ys α * rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j)
        rwa [mk_rep p h2 xs ys hxy j] at this))
    rw [Nat.card_congr e, card_cos_eq p h2 xs ys hxy l hpl]
    rfl
  rw [hcard]

/-- (3') the normalised operator: `T_l f (i) = Σ_j (N_ij / 2) f j`, with `T_l = Tn = U_l / 24`.
FINITE BOOKKEEPING. -/
theorem Tn_matrix [Fintype (Y p h2 xs ys hxy)] (l : ℕ) (hpl : ¬ p ∣ l)
    (f : Y p h2 xs ys hxy → ℂ) (i : Y p h2 xs ys hxy) :
    SectionA4g.Tn p h2 xs ys hxy l hpl f i
      = ∑ j, ((Tmat p h2 xs ys hxy l i j : ℚ) : ℂ) * f j := by
  unfold SectionA4g.Tn
  rw [U_matrix p h2 xs ys hxy l hpl f i, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold Tmat
  push_cast
  ring

#print axioms EdgeCount.card_cos_eq
#print axioms EdgeCount.card_end_symm
#print axioms EdgeCount.Tmat_symm
#print axioms EdgeCount.U_matrix
#print axioms EdgeCount.Tn_matrix

end EdgeCount
