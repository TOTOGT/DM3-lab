import StageA4o

/-!
# EDc7.lean   (UNTESTED until compiled by CI)

Splitting transport.  `RPEigen` quantifies over every `(xs, ys)` with `xs² + ys² = −1`, while a geometric
identification (Codogni-Lido, see the specialist package) fixes one splitting of `O ⊗ F_p`.  If two splittings are
conjugate, `red' x = c · red x · c⁻¹` on Hurwitz quaternions (Skolem-Noether, NOT proved here, taken as hypothesis `hc`),
this module proves the finite algebra that transports everything between them:

* `conjP c` : conjugation by `c` on `PGL₂(F_p)`.
* `Gam_conj` : `conjP c g ∈ Γ' ↔ g ∈ Γ`.
* `transport` : a bijection `e : Y_p ≃ Y_p'`, `Γ g ↦ Γ' (c g c⁻¹)`, with `χ' ∘ e = χ` and
  `U'_n (f ∘ e⁻¹) (e y) = U_n f y` for all admissible `n`, hence `T'_n` intertwined with `T_n`.
  Since `e` is a bijection, it is an isometry for the counting inner product, and `1 ↦ 1`.

What this does NOT do: it does not prove the conjugacy `hc` (an algebra statement about `red`), does not touch `RPEigen`,
and does not identify anything with elliptic curves.  `RPEigen` stays OPEN.
-/

namespace EDc7
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

variable (p : ℕ) [Fact p.Prime]

/-- conjugation by `c` on the center-quotient `PGL₂(F_p)`. -/
noncomputable def conjP (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : SectionA2.PGL2 p →* SectionA2.PGL2 p :=
  QuotientGroup.map _ _ (MulAut.conj c).toMonoidHom (by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz' := Subgroup.mem_center_iff.1 hz c
    have : (MulAut.conj c).toMonoidHom z = z := by
      show c * z * c⁻¹ = z
      rw [hz', mul_inv_cancel_right]
    rw [this]; exact hz)

theorem conjP_mk (c u : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) :
    conjP p c (QuotientGroup.mk u) = QuotientGroup.mk (c * u * c⁻¹) := rfl

theorem conjP_conjP_inv (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) (g : SectionA2.PGL2 p) :
    conjP p c⁻¹ (conjP p c g) = g := by
  induction g using QuotientGroup.induction_on with
  | H u =>
    rw [conjP_mk, conjP_mk]
    congr 1
    group

theorem conjP_inv_conjP (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) (g : SectionA2.PGL2 p) :
    conjP p c (conjP p c⁻¹ g) = g := by
  simpa using conjP_conjP_inv p c⁻¹ g

theorem conjP_injective (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Function.Injective (conjP p c) := by
  intro a b h
  have := congrArg (conjP p c⁻¹) h
  rwa [conjP_conjP_inv, conjP_conjP_inv] at this

noncomputable def conjE (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : SectionA2.PGL2 p ≃* SectionA2.PGL2 p where
  toFun := conjP p c
  invFun := conjP p c⁻¹
  left_inv := conjP_conjP_inv p c
  right_inv := conjP_inv_conjP p c
  map_mul' := (conjP p c).map_mul

variable (h2 : (2 : ZMod p) ≠ 0) (xs ys xs' ys' : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) (hxy' : xs' ^ 2 + ys' ^ 2 = -1)
  (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ)

/-- Hypothesis: the two splittings are conjugate on Hurwitz quaternions. -/
def Conj : Prop :=
  ∀ x : Quaternion ℚ, Section71d.QH x →
    Section74b.red p xs' ys' x = (c : Matrix (Fin 2) (Fin 2) (ZMod p)) * Section74b.red p xs ys x *
      ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p))

theorem rhoT_conj (hc : Conj p xs ys xs' ys' c) {x : Quaternion ℚ} (hx : Section71d.QH x) :
    SectionA4e.rhoT p xs' ys' x = conjP p c (SectionA4e.rhoT p xs ys x) := by
  by_cases hu : IsUnit (Section74b.red p xs ys x)
  · have hu' : IsUnit (Section74b.red p xs' ys' x) := by
      rw [hc x hx]
      exact (c.isUnit.mul hu).mul (c⁻¹).isUnit
    rw [SectionA4e.rhoT_of_unit p xs' ys' hu', SectionA4e.rhoT_of_unit p xs ys hu, conjP_mk]
    congr 1
    apply Units.ext
    rw [IsUnit.unit_spec, Units.val_mul, Units.val_mul, IsUnit.unit_spec]
    exact hc x hx
  · have hu' : ¬ IsUnit (Section74b.red p xs' ys' x) := by
      intro h
      apply hu
      have e : Section74b.red p xs ys x =
          ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
            Section74b.red p xs' ys' x * (c : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
        rw [hc x hx]
        simp [mul_assoc]
      rw [e]
      exact ((c⁻¹).isUnit.mul h).mul c.isUnit
    unfold SectionA4e.rhoT
    rw [dif_neg hu', dif_neg hu, map_one]

theorem rho_conj (hc : Conj p xs ys xs' ys' c) (u : SectionA3a2.HurU) :
    SectionA3a2.rho p h2 xs' ys' hxy' u = conjP p c (SectionA3a2.rho p h2 xs ys hxy u) := by
  show SectionA3a2.rhoFun p h2 xs' ys' hxy' u = conjP p c (SectionA3a2.rhoFun p h2 xs ys hxy u)
  unfold SectionA3a2.rhoFun
  rw [conjP_mk]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, SectionA2.redUnit_coe, SectionA2.redUnit_coe]
  exact hc _ (SectionA3a2.mem_iff _ |>.mp u.2).1

theorem Gam_conj (hc : Conj p xs ys xs' ys' c) (g : SectionA2.PGL2 p) :
    conjP p c g ∈ SectionA3b.Gam p h2 xs' ys' hxy' ↔ g ∈ SectionA3b.Gam p h2 xs ys hxy := by
  have hr : ∀ u : SectionA3a2.HurU, SectionA3a2.rho p h2 xs' ys' hxy' u
      = conjP p c (SectionA3a2.rho p h2 xs ys hxy u) :=
    fun u => rho_conj (p := p) (h2 := h2) (xs := xs) (ys := ys) (xs' := xs') (ys' := ys')
      (hxy := hxy) (hxy' := hxy') (c := c) hc u
  unfold SectionA3b.Gam
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply conjP_injective p c
    rw [← hu, hr u]
  · rintro ⟨u, rfl⟩
    exact ⟨u, hr u⟩

theorem chiP_conj (g : SectionA2.PGL2 p) :
    SectionA4k.chiP p (conjP p c g) = SectionA4k.chiP p g := by
  induction g using QuotientGroup.induction_on with
  | H u =>
    first
    | (rw [conjP_mk, SectionA4k.chiP_mk, SectionA4k.chiP_mk, map_mul, map_mul, map_inv,
          mul_comm (SectionA4k.chiGL p c) (SectionA4k.chiGL p u), mul_inv_cancel_right])
    | simp [conjP_mk, SectionA4k.chiP_mk, map_mul, map_inv, mul_comm]

theorem transport (hc : Conj p xs ys xs' ys' c) :
    ∃ e : SectionA3b.Yp p h2 xs ys hxy ≃ SectionA3b.Yp p h2 xs' ys' hxy',
      (∀ g, e (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g)
        = Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs' ys' hxy')) (conjP p c g)) ∧
      (∀ y, SectionA4k.chiY p h2 xs' ys' hxy' (e y) = SectionA4k.chiY p h2 xs ys hxy y) ∧
      (∀ (n : ℕ) (hn : ¬ p ∣ n) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ)
        (y : SectionA3b.Yp p h2 xs ys hxy),
        SectionA4e.U p h2 xs' ys' hxy' n hn (f ∘ e.symm) (e y)
          = SectionA4e.U p h2 xs ys hxy n hn f y) := by
  have hG := fun g => Gam_conj (p := p) (h2 := h2) (xs := xs) (ys := ys) (xs' := xs') (ys' := ys')
    (hxy := hxy) (hxy' := hxy') (c := c) hc g
  let e : SectionA3b.Yp p h2 xs ys hxy ≃ SectionA3b.Yp p h2 xs' ys' hxy' :=
    Quotient.congr (conjE p c).toEquiv (by
      intro a b
      constructor
      · intro h
        have h' := QuotientGroup.rightRel_apply.1 h
        apply QuotientGroup.rightRel_apply.2
        show conjP p c b * (conjP p c a)⁻¹ ∈ SectionA3b.Gam p h2 xs' ys' hxy'
        rw [← map_inv, ← map_mul]
        exact (hG _).2 h'
      · intro h
        have h' := QuotientGroup.rightRel_apply.1 h
        apply QuotientGroup.rightRel_apply.2
        have h'' : conjP p c b * (conjP p c a)⁻¹ ∈ SectionA3b.Gam p h2 xs' ys' hxy' := h'
        rw [← map_inv, ← map_mul] at h''
        exact (hG _).1 h'')
  have he : ∀ g, e (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g)
      = Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs' ys' hxy')) (conjP p c g) :=
    fun g => rfl
  refine ⟨e, he, ?_, ?_⟩
  · intro y
    refine Quotient.inductionOn y (fun g => ?_)
    rw [he g, SectionA4k.chiY_mk, SectionA4k.chiY_mk, chiP_conj]
  · intro n hn f y
    refine Quotient.inductionOn y (fun g => ?_)
    rw [he g, SectionA4e.U_mk p h2 xs' ys' hxy' n hn (f ∘ e.symm) (conjP p c g),
      SectionA4e.U_mk p h2 xs ys hxy n hn f g]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    obtain ⟨hxQ, _⟩ := (Set.Finite.mem_toFinset _).1 hx
    rw [rhoT_conj (p := p) (xs := xs) (ys := ys) (xs' := xs') (ys' := ys') (c := c) hc hxQ,
      ← map_mul]
    show f (e.symm (e (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (SectionA4e.rhoT p xs ys x * g))))
      = f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (SectionA4e.rhoT p xs ys x * g))
    rw [e.symm_apply_apply]

end EDc7

#print axioms EDc7.conjP_conjP_inv
#print axioms EDc7.conjP_injective
#print axioms EDc7.rhoT_conj
#print axioms EDc7.rho_conj
#print axioms EDc7.Gam_conj
#print axioms EDc7.chiP_conj
#print axioms EDc7.transport
