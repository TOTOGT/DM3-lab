import UnitEndpointOrbits

/-!
UNTESTED DRAFT v3 (2026-11-25). NOT in any repository. Nothing here has been compiled.
Finite algebra only. No geometric or spectral content. RPEigen stays OPEN.

Base for names and signatures: DM3-lab main b164de7 (read verbatim from
EDc11.lean, UnitEndpointOrbits.lean, VertexDoubleOrbit.lean, StageA3a2.lean, StageA3a3.lean).

What this file is meant to establish (read against the code, not the names):
  (T0) Tmat_eq_card_orbits : (Tmat i j : ℚ) = number of left-unit orbits on NCos (rep i) (rep j).
       In particular the matrix entry N_ij / 2 is a natural number.
  (T1) two_mul_card_cosetOrbits : 2 * #orbits = #NEnd.
  (T2) card_cos_eq_twentyfour_mul_orbits : #NCos = 24 * #orbits.
Route: the kernel of rho acts freely on NEnd by left multiplication; its orbits are the residual
classes (residual_iff); so NEnd ≃ (residual classes) × ker rho (no Finite hypothesis needed);
card_ker = 2; orbitEquiv identifies residual classes with unit orbits on NCos; card_cos_eq gives 12.

Design choices taken from the two earlier drafts:
  * from v2: the equivalence Quotient × ker ≃ NEnd (no Finite hypothesis, no sigma-sum);
  * from v1: the explicit target statements T1, T2 and their derivations.
Dropped: the `GeomModel` / `CLSpectralBound` interface of v1 (see the report: with V := Y it is
satisfiable by the identity, so it does not separate geometry from the conclusion).

Names used that already appear in CI-compiled repo files: Nat.card_prod, Nat.card_congr,
Equiv.ofBijective, Quotient.out_eq, Quotient.exact, Quotient.sound, mul_right_cancel.
Names NOT re-checked: MonoidHom.mem_ker (standard), mul_right_cancel₀ (v2 reports it read in Defs.lean).
-/

namespace EdgeMultiplicity

open SectionA3a2 SectionA3a3 EdgeCount EdgeUnitOrbits

/-- `qv` is injective on `HurU` (it is the coercion to the unit's value). -/
theorem qv_inj {u v : HurU} (huv : qv u = qv v) : u = v :=
  Subtype.ext (Units.ext huv)

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
  (l : ℕ) (hpl : ¬ p ∣ l) (g h : SectionA2.PGL2 p)

include h2 hxy hpl

/-- Every exact endpoint is nonzero: its norm is `l ≠ 0` because `¬ p ∣ l`. -/
theorem val_ne_zero (a : NEnd p xs ys l g h) : a.val ≠ 0 := by
  intro h0
  have hn := a.property.1.2
  rw [h0, map_zero] at hn
  have hl : l = 0 := by exact_mod_cast hn.symm
  exact hpl (by rw [hl]; exact dvd_zero p)

/-- Left multiplication by a kernel unit preserves exact endpoints. -/
noncomputable def actKer (u : (SectionA3a2.rho p h2 xs ys hxy).ker)
    (a : NEnd p xs ys l g h) : NEnd p xs ys l g h :=
  ⟨qv (u : HurU) * a.val,
    (leftAct p h2 xs ys hxy (u : HurU) l hpl a.property.1).1,
    by
      have hact := (leftAct p h2 xs ys hxy (u : HurU) l hpl a.property.1).2
      have hu : SectionA3a2.rho p h2 xs ys hxy (u : HurU) = 1 := MonoidHom.mem_ker.1 u.2
      rw [hact, hu, one_mul]
      exact a.property.2⟩

/-- The pairing (residual class, kernel element) ↦ exact endpoint, using the chosen representative. -/
noncomputable def kerOrbit :
    Quotient (residualSetoid p xs ys l g h) × (SectionA3a2.rho p h2 xs ys hxy).ker →
      NEnd p xs ys l g h :=
  fun x => actKer p h2 xs ys hxy l hpl g h x.2 (Quotient.out x.1)

theorem kerOrbit_injective : Function.Injective (kerOrbit p h2 xs ys hxy l hpl g h) := by
  rintro ⟨q, u⟩ ⟨q', u'⟩ heq
  have heq' : actKer p h2 xs ys hxy l hpl g h u (Quotient.out q)
      = actKer p h2 xs ys hxy l hpl g h u' (Quotient.out q') := heq
  have e1 : Quotient.mk (residualSetoid p xs ys l g h) (Quotient.out q) =
      Quotient.mk _ (actKer p h2 xs ys hxy l hpl g h u (Quotient.out q)) :=
    Quotient.sound ⟨(u : HurU), rfl⟩
  have e2 : Quotient.mk (residualSetoid p xs ys l g h) (Quotient.out q') =
      Quotient.mk _ (actKer p h2 xs ys hxy l hpl g h u' (Quotient.out q')) :=
    Quotient.sound ⟨(u' : HurU), rfl⟩
  have hq : q = q' := by
    calc q = Quotient.mk (residualSetoid p xs ys l g h) (Quotient.out q) := (Quotient.out_eq q).symm
      _ = Quotient.mk _ (actKer p h2 xs ys hxy l hpl g h u (Quotient.out q)) := e1
      _ = Quotient.mk _ (actKer p h2 xs ys hxy l hpl g h u' (Quotient.out q')) := by rw [heq']
      _ = Quotient.mk (residualSetoid p xs ys l g h) (Quotient.out q') := e2.symm
      _ = q' := Quotient.out_eq q'
  have ho : Quotient.out q' = Quotient.out q := by rw [hq]
  rw [ho] at heq'
  have hv : qv (u : HurU) * (Quotient.out q).val = qv (u' : HurU) * (Quotient.out q).val :=
    congrArg Subtype.val heq'
  have hcancel := mul_right_cancel₀ (val_ne_zero p h2 xs ys hxy l hpl g h (Quotient.out q)) hv
  exact Prod.ext hq (Subtype.ext (qv_inj hcancel))

theorem kerOrbit_surjective : Function.Surjective (kerOrbit p h2 xs ys hxy l hpl g h) := by
  intro a
  have hr : (residualSetoid p xs ys l g h).r
      (Quotient.out (Quotient.mk (residualSetoid p xs ys l g h) a)) a :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (residualSetoid p xs ys l g h) a))
  obtain ⟨u, hu1, hu2⟩ := (residual_iff p h2 xs ys hxy l hpl g h _ _).1 hr
  exact ⟨(Quotient.mk _ a, ⟨u, MonoidHom.mem_ker.2 hu1⟩), Subtype.ext hu2⟩

/-- `#NEnd = 2 * #(residual classes)`. No finiteness hypothesis. -/
theorem card_end_eq_two_mul_card_residual :
    Nat.card (NEnd p xs ys l g h) =
      2 * Nat.card (Quotient (residualSetoid p xs ys l g h)) := by
  have e := Equiv.ofBijective _
    ⟨kerOrbit_injective p h2 xs ys hxy l hpl g h, kerOrbit_surjective p h2 xs ys hxy l hpl g h⟩
  rw [← Nat.card_congr e, Nat.card_prod, SectionA3a2.card_ker p h2 xs ys hxy, mul_comm]

/-- (T1) `2 * #(unit orbits on NCos) = #NEnd`. -/
theorem two_mul_card_cosetOrbits :
    2 * Nat.card (Quotient (cosetSetoid p h2 xs ys hxy l g h)) =
      Nat.card (NEnd p xs ys l g h) := by
  rw [card_end_eq_two_mul_card_residual p h2 xs ys hxy l hpl g h,
    Nat.card_congr (orbitEquiv p h2 xs ys hxy l hpl g h)]

/-- (T2) `#NCos = 24 * #(unit orbits on NCos)`. -/
theorem card_cos_eq_twentyfour_mul_orbits :
    Nat.card (NCos p h2 xs ys hxy l g h) =
      24 * Nat.card (Quotient (cosetSetoid p h2 xs ys hxy l g h)) := by
  have h1 := card_cos_eq p h2 xs ys hxy l hpl g h
  have h3 := two_mul_card_cosetOrbits p h2 xs ys hxy l hpl g h
  omega

/-- (T0) The Hecke matrix entry is the number of unit orbits (so it is a natural number). -/
theorem Tmat_eq_card_orbits (i j : Y p h2 xs ys hxy) :
    Tmat p h2 xs ys hxy l i j =
      ((Nat.card (Quotient (cosetSetoid p h2 xs ys hxy l
        (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j))) : ℕ) : ℚ) := by
  have h1 := two_mul_card_cosetOrbits p h2 xs ys hxy l hpl
    (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j)
  have h1' : (2 : ℚ) * ((Nat.card (Quotient (cosetSetoid p h2 xs ys hxy l
        (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j))) : ℕ) : ℚ) =
      ((Nat.card (NEnd p xs ys l (rep p h2 xs ys hxy i) (rep p h2 xs ys hxy j)) : ℕ) : ℚ) := by
    exact_mod_cast h1
  unfold Tmat Nmat
  rw [← h1']
  ring

end EdgeMultiplicity

#print axioms EdgeMultiplicity.card_end_eq_two_mul_card_residual
#print axioms EdgeMultiplicity.two_mul_card_cosetOrbits
#print axioms EdgeMultiplicity.card_cos_eq_twentyfour_mul_orbits
#print axioms EdgeMultiplicity.Tmat_eq_card_orbits
