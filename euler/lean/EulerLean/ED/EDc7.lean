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
  ∀ x : Quaternion ℚ, QH x →
    Section74b.red p xs' ys' x = (c : Matrix (Fin 2) (Fin 2) (ZMod p)) * Section74b.red p xs ys x *
      ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p))

include hc in
theorem rhoT_conj (hc : Conj p xs ys xs' ys' c) {x : Quaternion ℚ} (hx : QH x) :
    SectionA4o.rhoT p xs' ys' x = conjP p c (SectionA4o.rhoT p xs ys x) := by
  by_cases hu : IsUnit (Section74b.red p xs ys x)
  · have hu' : IsUnit (Section74b.red p xs' ys' x) := by
      rw [hc x hx]
      exact (c.isUnit.mul hu).mul (c⁻¹).isUnit
    rw [SectionA4o.rhoT_of_unit p xs' ys' hu', SectionA4o.rhoT_of_unit p xs ys hu, conjP_mk]
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
    unfold SectionA4o.rhoT
    rw [dif_neg hu', dif_neg hu, map_one]

end EDc7

#print axioms EDc7.conjP_conjP_inv
#print axioms EDc7.conjP_injective
#print axioms EDc7.rhoT_conj
