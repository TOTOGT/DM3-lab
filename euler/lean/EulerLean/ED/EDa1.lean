import Mathlib

namespace EDa1

variable (p : ℕ) [Fact p.Prime]

/-- PGL2 over F_p presented as units of 2x2 matrices modulo the center (same definition as SectionA2.PGL2). -/
abbrev PGL2 : Type :=
  (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ ⧸ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ

theorem card_GL2 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem card_center : Nat.card (Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) = p - 1 := by
  have h : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := ZMod p)).range :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := ZMod p)) := by
    intro a b hab
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hab
    simp [Matrix.GeneralLinearGroup.scalar] at this
    exact Units.ext this
  have : Nat.card (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) = Nat.card (ZMod p)ˣ := by
    rw [h]
    exact (Nat.card_congr (Equiv.ofInjective _ hinj).symm)
  rw [show Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ =
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) from rfl, this]
  rw [Nat.card_units, Nat.card_zmod]

theorem card_PGL2 : Nat.card (PGL2 p) * (p - 1) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ)
  rw [card_center p] at h
  have h2 := card_GL2 p
  rw [show Matrix.GeneralLinearGroup (Fin 2) (ZMod p) = (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ from rfl] at h2
  rw [h] at h2
  exact h2

theorem card_PGL2_eq : Nat.card (PGL2 p) = p * (p ^ 2 - 1) := by
  have h := card_PGL2 p
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 0 < p - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hp1
  rw [h]
  have e : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub, pow_two, mul_one]
  rw [e]
  ring

end EDa1

#print axioms EDa1.card_PGL2
#print axioms EDa1.card_PGL2_eq
