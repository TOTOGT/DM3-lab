import EDc10

/-! Orbit types for units on the left and nonzero scalars on the right.
No normality of Gamma, geometric identification, or spectral result is assumed. -/
namespace EulerVertexOrbit
open EulerVertexDraft

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- Equivalence relation pulled back from the left Gamma-orbit type. -/
noncomputable def doubleOrbitSetoid : Setoid (MatrixUnits p) :=
  Setoid.comap (projectivize p)
    (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))

/-- This is exactly the unit-left/scalar-right double-orbit relation. -/
theorem doubleOrbitRel_iff (a b : MatrixUnits p) :
    (doubleOrbitSetoid p h2 xs ys hxy).r a b ↔
      ∃ (u : SectionA3a2.HurU) (c : (ZMod p)ˣ),
        b = unitRed p h2 xs ys hxy u * a *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  change QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)
    (projectivize p a) (projectivize p b) ↔ _
  rw [QuotientGroup.rightRel_apply]
  change projectivize p b * (projectivize p a)⁻¹ ∈
    (SectionA3a2.rho p h2 xs ys hxy).range ↔ _
  constructor
  · rintro ⟨u, hu⟩
    let z := (unitRed p h2 xs ys hxy u * a)⁻¹ * b
    have hz : z ∈ Subgroup.center (MatrixUnits p) := by
      apply (QuotientGroup.eq_one_iff z).mp
      change projectivize p z = 1
      dsimp [z]
      rw [map_mul, map_inv, map_mul, projectivize_unitRed, hu]
      group
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨c, hc⟩ := hz
    refine ⟨u, c, ?_⟩
    rw [hc]
    dsimp [z]
    group
  · rintro ⟨u, c, rfl⟩
    refine ⟨u, ?_⟩
    have hc : projectivize p (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [map_mul, map_mul, hc, mul_one, projectivize_unitRed]
    group

/-- U\GL2/(F_p^* I) is a type of orbits, equivalent to Gamma\PGL2. -/
noncomputable def doubleOrbitEquiv :
    Quotient (doubleOrbitSetoid p h2 xs ys hxy) ≃ SectionA3b.Yp p h2 xs ys hxy := by
  let F : Quotient (doubleOrbitSetoid p h2 xs ys hxy) → SectionA3b.Yp p h2 xs ys hxy :=
    Quotient.lift (fun a => Quotient.mk _ (projectivize p a))
      (fun _ _ h => Quotient.sound h)
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b (fun a b => ?_)
    intro h
    have h' : (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (projectivize p a)) = Quotient.mk _ (projectivize p b) := h
    apply Quotient.sound
    change QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)
      (projectivize p a) (projectivize p b)
    exact Quotient.exact h'
  · intro y
    refine Quotient.inductionOn y (fun g => ?_)
    obtain ⟨a, rfl⟩ := projectivize_surjective p g
    exact ⟨Quotient.mk _ a, rfl⟩

/-- Representative formula fixes the orientation of the equivalence. -/
theorem doubleOrbitEquiv_mk (a : MatrixUnits p) :
    doubleOrbitEquiv p h2 xs ys hxy (Quotient.mk _ a) =
      Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
        (projectivize p a) := rfl

/-- The unit stabilizer subgroup is independent of the projective point. -/
theorem stabilizer_eq_kernel (g : SectionA2.PGL2 p) :
    {u : SectionA3a2.HurU | SectionA3a2.rho p h2 xs ys hxy u * g = g} =
      ((SectionA3a2.rho p h2 xs ys hxy).ker : Set SectionA3a2.HurU) := by
  ext u
  change SectionA3a2.rho p h2 xs ys hxy u * g = g ↔
    SectionA3a2.rho p h2 xs ys hxy u = 1
  exact ⟨fun h => SectionA3b.free_left p _ _ h, fun h => by rw [h, one_mul]⟩

/-- There are uniformly two stabilizing units, namely the already checked ±1 kernel. -/
theorem stabilizer_card (g : SectionA2.PGL2 p) :
    Nat.card {u : SectionA3a2.HurU // SectionA3a2.rho p h2 xs ys hxy u * g = g} = 2 := by
  change Nat.card ↥({u : SectionA3a2.HurU | SectionA3a2.rho p h2 xs ys hxy u * g = g}) = 2
  rw [stabilizer_eq_kernel]
  exact SectionA3a2.card_ker p h2 xs ys hxy

end EulerVertexOrbit

#print axioms EulerVertexOrbit.doubleOrbitRel_iff
#print axioms EulerVertexOrbit.doubleOrbitEquiv
#print axioms EulerVertexOrbit.doubleOrbitEquiv_mk
#print axioms EulerVertexOrbit.stabilizer_eq_kernel
#print axioms EulerVertexOrbit.stabilizer_card
#check EulerVertexOrbit.doubleOrbitRel_iff
#check EulerVertexOrbit.doubleOrbitEquiv
#check EulerVertexOrbit.stabilizer_eq_kernel
#check EulerVertexOrbit.stabilizer_card
