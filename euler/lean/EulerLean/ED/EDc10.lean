import StageA4o

/-!
UNTESTED: not compiled anywhere. Draft against the names in StageA4o.lean
(working copy; check the tracked commit before promoting). CI is the only compiler.

Revised from handoff/VertexBridge.lean. Changes: fixed the injectivity proof in
`quotientComapEquiv` (hypothesis depended on the eliminated variables), removed `let`/`group`
from `mem_liftedGamma_iff`, added the kernel and 24 = 12 * 2 lemmas below.

Names grepped in StageA4o.lean: SectionA2.PGL2, SectionA2.redUnit, SectionA3a.not_dvd_one_p,
SectionA3a2.HurU, .mem_iff, .rho, .negOne, .rho_eq_one_iff, .card_ker, .card_range_mul_two,
SectionA3a3.card_HurU, SectionA3b.Gam, .card_Gam, .Yp, .free_left.
Unverified Mathlib names: QuotientGroup.rightRel_apply, QuotientGroup.eq_one_iff,
QuotientGroup.mk', Subgroup.mem_comap, Quotient.inductionOn/inductionOn₂, Equiv.ofBijective.

KIND OF RESULT: finite bookkeeping (group theory on already-defined objects).

ESTABLISHES (if it compiles):
 * coset spaces of a preimage subgroup under a surjection = coset spaces of the target subgroup;
 * the linear-level quotient GL2(F_p)/liftedGamma is equivalent to Yp;
 * g in liftedGamma iff g = (unit reduction) * (central unit);
 * the kernel of rho : HurU ->* PGL2(F_p) is exactly {1, -1}; a Hurwitz unit reduces to a central
   matrix iff it is +-1; Hurwitz units fix no point of PGL2(F_p) other than by being +-1;
 * Nat.card HurU = Nat.card Gam * Nat.card ker rho, i.e. 24 = 12 * 2.
 The kernel lemma has NO hypothesis p > 3: it is exactly SectionA3a2.rho_eq_one_iff, which needs only
 2 /= 0 in ZMod p, a square root of -1 as (xs, ys) and p prime. Whether p = 3 is meaningful is not
 argued here.

DOES NOT ESTABLISH: any elliptic curve statement, Deuring correspondence, the bijection of Yp with
supersingular vertices, injectivity of Aut(E0) -> GL2(F_p) (external hypothesis, not assumed here),
isogeny graph, spectral estimate. RPEigen is OPEN and not used.
-/

namespace EulerVertexDraft

/-- Cosets of the preimage of H under a surjection match cosets of H (types only). -/
noncomputable def quotientComapEquiv
    {G P : Type*} [Group G] [Group P]
    (q : G →* P) (hq : Function.Surjective q) (H : Subgroup P) :
    Quotient (QuotientGroup.rightRel (H.comap q)) ≃
      Quotient (QuotientGroup.rightRel H) := by
  have hrel (a b : G) :
      QuotientGroup.rightRel (H.comap q) a b ↔
        QuotientGroup.rightRel H (q a) (q b) := by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change q (b * a⁻¹) ∈ H ↔ q b * (q a)⁻¹ ∈ H
    rw [map_mul, map_inv]
  let F : Quotient (QuotientGroup.rightRel (H.comap q)) →
      Quotient (QuotientGroup.rightRel H) :=
    Quotient.lift (fun a => Quotient.mk (QuotientGroup.rightRel H) (q a))
      (fun a b hab => Quotient.sound ((hrel a b).mp hab))
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b (fun a b => ?_)
    intro hab
    have hab' : (Quotient.mk (QuotientGroup.rightRel H) (q a)) =
        Quotient.mk (QuotientGroup.rightRel H) (q b) := hab
    exact Quotient.sound ((hrel a b).mpr (Quotient.exact hab'))
  · intro y
    refine Quotient.inductionOn y ?_
    intro y
    obtain ⟨g, rfl⟩ := hq y
    exact ⟨Quotient.mk _ g, rfl⟩

variable (p : ℕ) [Fact p.Prime]

abbrev MatrixUnits : Type := (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ

noncomputable def projectivize : MatrixUnits p →* SectionA2.PGL2 p :=
  QuotientGroup.mk' (Subgroup.center (MatrixUnits p))

theorem projectivize_surjective : Function.Surjective (projectivize p) := by
  intro g
  refine Quotient.inductionOn g ?_
  intro a
  exact ⟨a, rfl⟩

variable (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- Subgroup of GL2(F_p) whose projective image lies in Gam. -/
noncomputable def liftedGamma : Subgroup (MatrixUnits p) :=
  (SectionA3b.Gam p h2 xs ys hxy).comap (projectivize p)

/-- GL2-level cosets of liftedGamma are exactly Yp. -/
noncomputable def linearLevelVertexEquiv :
    Quotient (QuotientGroup.rightRel (liftedGamma p h2 xs ys hxy)) ≃
      SectionA3b.Yp p h2 xs ys hxy :=
  quotientComapEquiv (projectivize p) (projectivize_surjective p)
    (SectionA3b.Gam p h2 xs ys hxy)

/-- The GL2(F_p) unit that rho projectivizes (same data as `SectionA3a2.rhoFun`). -/
noncomputable def unitRed (u : SectionA3a2.HurU) : MatrixUnits p :=
  SectionA2.redUnit p h2 xs ys hxy
    (SectionA3a2.mem_iff _ |>.mp u.2).1 1
    (by rw [(SectionA3a2.mem_iff _ |>.mp u.2).2]; norm_num)
    (SectionA3a.not_dvd_one_p p)

theorem projectivize_unitRed (u : SectionA3a2.HurU) :
    projectivize p (unitRed p h2 xs ys hxy u) =
      SectionA3a2.rho p h2 xs ys hxy u := rfl

theorem mem_liftedGamma_iff (g : MatrixUnits p) :
    g ∈ liftedGamma p h2 xs ys hxy ↔
      ∃ u : SectionA3a2.HurU, ∃ z : MatrixUnits p,
        z ∈ Subgroup.center (MatrixUnits p) ∧
          g = unitRed p h2 xs ys hxy u * z := by
  change projectivize p g ∈ (SectionA3a2.rho p h2 xs ys hxy).range ↔ _
  constructor
  · rintro ⟨u, hu⟩
    have hz : (unitRed p h2 xs ys hxy u)⁻¹ * g ∈ Subgroup.center (MatrixUnits p) := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change projectivize p ((unitRed p h2 xs ys hxy u)⁻¹ * g) = 1
      rw [map_mul, map_inv, projectivize_unitRed, hu, inv_mul_cancel]
    exact ⟨u, _, hz, (mul_inv_cancel_left _ _).symm⟩
  · rintro ⟨u, z, hz, rfl⟩
    refine ⟨u, ?_⟩
    have hz' : projectivize p z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [map_mul, projectivize_unitRed, hz', mul_one]

/-- Hurwitz units fix a point of PGL2(F_p) under left multiplication iff they are +-1. -/
theorem unit_stabilizer_iff (u : SectionA3a2.HurU) (g : SectionA2.PGL2 p) :
    SectionA3a2.rho p h2 xs ys hxy u * g = g ↔
      u = 1 ∨ u = SectionA3a2.negOne := by
  rw [← SectionA3a2.rho_eq_one_iff p h2 xs ys hxy u]
  constructor
  · intro h
    exact mul_right_cancel (h.trans (one_mul g).symm)
  · intro h
    rw [h, one_mul]

/-! ### Kernel of Hurwitz units -> PGL2(F_p), and 24 = 12 * 2 (finite bookkeeping) -/

/-- Kernel of rho is exactly {1, -1}. No p > 3 needed beyond the hypotheses of rho_eq_one_iff. -/
theorem mem_ker_rho_iff (u : SectionA3a2.HurU) :
    u ∈ (SectionA3a2.rho p h2 xs ys hxy).ker ↔ u = 1 ∨ u = SectionA3a2.negOne :=
  SectionA3a2.rho_eq_one_iff p h2 xs ys hxy u

theorem card_ker_rho : Nat.card (SectionA3a2.rho p h2 xs ys hxy).ker = 2 :=
  SectionA3a2.card_ker p h2 xs ys hxy

/-- A Hurwitz unit reduces to a central matrix unit iff it is +-1. -/
theorem unitRed_central_iff (u : SectionA3a2.HurU) :
    unitRed p h2 xs ys hxy u ∈ Subgroup.center (MatrixUnits p) ↔
      u = 1 ∨ u = SectionA3a2.negOne := by
  rw [← QuotientGroup.eq_one_iff (N := Subgroup.center (MatrixUnits p))]
  exact SectionA3a2.rho_eq_one_iff p h2 xs ys hxy u

/-- 24 = 12 * 2 : |Hurwitz units| = |Gam| * |ker rho|, from card_HurU, card_Gam, card_ker. -/
theorem card_HurU_eq_card_Gam_mul_card_ker :
    Nat.card SectionA3a2.HurU =
      Nat.card (SectionA3b.Gam p h2 xs ys hxy) *
        Nat.card (SectionA3a2.rho p h2 xs ys hxy).ker := by
  rw [SectionA3a3.card_HurU, SectionA3b.card_Gam p h2 xs ys hxy,
    SectionA3a2.card_ker p h2 xs ys hxy]

theorem card_HurU_twelve_two :
    Nat.card SectionA3a2.HurU = 12 * 2 := by
  rw [SectionA3a3.card_HurU]

end EulerVertexDraft

#print axioms EulerVertexDraft.linearLevelVertexEquiv
#print axioms EulerVertexDraft.mem_liftedGamma_iff
#print axioms EulerVertexDraft.unit_stabilizer_iff
#print axioms EulerVertexDraft.mem_ker_rho_iff
#print axioms EulerVertexDraft.unitRed_central_iff
#print axioms EulerVertexDraft.card_HurU_eq_card_Gam_mul_card_ker
#print axioms EulerVertexDraft.card_HurU_twelve_two
