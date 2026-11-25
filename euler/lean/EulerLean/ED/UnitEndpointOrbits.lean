import EDc11

/-!
Unit orbits of coset endpoints and residual-kernel orbits of exact endpoints.
Finite algebra only. This module supplies no geometric or spectral identification.
-/

namespace EdgeUnitOrbits

open SectionA3a2 SectionA3a3 EdgeCount

/-- Left multiplication by a Hurwitz unit, as an equivalence relation. -/
def unitSetoid : Setoid (Quaternion ℚ) where
  r a b := ∃ u : HurU, qv u * a = b
  iseqv := {
    refl := fun a => ⟨1, by simp [qv]⟩
    symm := by
      rintro a b ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [← hu]
      exact qv_inv_mul u a
    trans := by
      rintro a b c ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨v * u, ?_⟩
      change (qv v * qv u) * a = c
      rw [mul_assoc, hu, hv]
  }

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
  (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p)

/-- Unit-orbit relation on the coset endpoint set. -/
def cosetSetoid : Setoid (NCos p h2 xs ys hxy l g h) :=
  Setoid.comap Subtype.val unitSetoid

/-- Restriction to exact endpoints; characterized below by the residual kernel. -/
def residualSetoid : Setoid (NEnd p xs ys l g h) :=
  Setoid.comap Subtype.val unitSetoid

include hpl in
/-- Between exact endpoints, precisely the units in ker rho can act. -/
theorem residual_iff (a b : NEnd p xs ys l g h) :
    (residualSetoid p xs ys l g h).r a b ↔
      ∃ u : HurU, SectionA3a2.rho p h2 xs ys hxy u = 1 ∧ qv u * a.val = b.val := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_, hu⟩
    have he := (leftAct p h2 xs ys hxy u l hpl a.property.1).2
    rw [hu] at he
    have hend := congrArg (fun z : SectionA2.PGL2 p => z * g) he
    rw [mul_assoc, a.property.2, b.property.2] at hend
    exact mul_right_cancel (show SectionA3a2.rho p h2 xs ys hxy u * h = 1 * h by
      simpa using hend.symm)
  · rintro ⟨u, _, hu⟩
    exact ⟨u, hu⟩

/-- Inclusion of the exact endpoint fibre into the coset endpoint fibre. -/
def exactToCos (a : NEnd p xs ys l g h) : NCos p h2 xs ys hxy l g h :=
  ⟨a.val, a.property.1, 1, (SectionA3b.Gam p h2 xs ys hxy).one_mem,
    by simpa using a.property.2⟩

/-- The map on orbit types induced by inclusion of exact endpoints. -/
def orbitMap :
    Quotient (residualSetoid p xs ys l g h) →
      Quotient (cosetSetoid p h2 xs ys hxy l g h) :=
  Quotient.map (exactToCos p h2 xs ys hxy l g h) (fun _ _ hab => hab)

theorem orbitMap_injective :
    Function.Injective (orbitMap p h2 xs ys hxy l g h) := by
  intro a b
  refine Quotient.inductionOn₂ a b (fun x y heq => ?_)
  have hrel : (cosetSetoid p h2 xs ys hxy l g h).r
      (exactToCos p h2 xs ys hxy l g h x)
      (exactToCos p h2 xs ys hxy l g h y) := Quotient.exact heq
  exact Quotient.sound hrel

include hpl in
theorem orbitMap_surjective :
    Function.Surjective (orbitMap p h2 xs ys hxy l g h) := by
  intro a
  refine Quotient.inductionOn a (fun x => ?_)
  obtain ⟨γ, hγ, hend⟩ := x.property.2
  let u := uOf p h2 xs ys hxy ⟨γ, hγ⟩
  have hrho : SectionA3a2.rho p h2 xs ys hxy u = γ :=
    uOf_spec p h2 xs ys hxy ⟨γ, hγ⟩
  have hact := leftAct p h2 xs ys hxy u⁻¹ l hpl x.property.1
  have hexact : SectionA4e.rhoT p xs ys (qv u⁻¹ * x.val) * g = h := by
    rw [hact.2, map_inv, hrho, mul_assoc, hend, inv_mul_cancel_left]
  let y : NEnd p xs ys l g h := ⟨qv u⁻¹ * x.val, hact.1, hexact⟩
  refine ⟨Quotient.mk _ y, ?_⟩
  apply Quotient.sound
  exact ⟨u, qv_mul_inv u x.val⟩

/-- Unit orbits of coset endpoints equal residual-kernel orbits of exact endpoints. -/
noncomputable def orbitEquiv :
    Quotient (residualSetoid p xs ys l g h) ≃
      Quotient (cosetSetoid p h2 xs ys hxy l g h) :=
  Equiv.ofBijective _ ⟨orbitMap_injective p h2 xs ys hxy l g h,
    orbitMap_surjective p h2 xs ys hxy l hpl g h⟩

end EdgeUnitOrbits

#print axioms EdgeUnitOrbits.residual_iff
#print axioms EdgeUnitOrbits.orbitMap_injective
#print axioms EdgeUnitOrbits.orbitMap_surjective
#print axioms EdgeUnitOrbits.orbitEquiv
#check EdgeUnitOrbits.residual_iff
#check EdgeUnitOrbits.orbitEquiv

#check EdgeUnitOrbits.orbitMap_injective
#check EdgeUnitOrbits.orbitMap_surjective
