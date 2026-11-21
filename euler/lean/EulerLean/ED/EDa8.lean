import StageA4o
import EDa6

namespace EDa8
open EDa4
variable (p : ℕ) [Fact p.Prime]

theorem mk_eq_smul (a b : GL2 p) (h : (QuotientGroup.mk a : PGL2 p) = QuotientGroup.mk b) :
    ∃ c : ZMod p, ((b : Matrix (Fin 2) (Fin 2) (ZMod p))) = c • (a : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  have h1 := QuotientGroup.eq.1 h
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c, ?_⟩
  have : b = a * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    rw [hc]; group
  rw [this]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_eq_diagonal_mul]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

end EDa8

namespace EDa8
open EDa4
variable (p : ℕ) [Fact p.Prime]

theorem rhoT_eq_smul (xs ys : ZMod p) {x y : Quaternion ℚ}
    (hx : IsUnit (Section74b.red p xs ys x)) (hy : IsUnit (Section74b.red p xs ys y))
    (h : SectionA4e.rhoT p xs ys x = SectionA4e.rhoT p xs ys y) :
    ∃ c : ZMod p, Section74b.red p xs ys y = c • Section74b.red p xs ys x := by
  rw [SectionA4e.rhoT_of_unit p xs ys hx, SectionA4e.rhoT_of_unit p xs ys hy] at h
  obtain ⟨c, hc⟩ := mk_eq_smul p _ _ h
  exact ⟨c, by simpa using hc⟩

theorem rhoT_eq_one_smul (xs ys : ZMod p) {x : Quaternion ℚ}
    (hx : IsUnit (Section74b.red p xs ys x))
    (h : SectionA4e.rhoT p xs ys x = 1) :
    ∃ c : ZMod p, (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = c • Section74b.red p xs ys x := by
  rw [SectionA4e.rhoT_of_unit p xs ys hx] at h
  have h' : (QuotientGroup.mk hx.unit : PGL2 p) = QuotientGroup.mk (1 : GL2 p) := h
  obtain ⟨c, hc⟩ := mk_eq_smul p _ _ h'
  exact ⟨c, by simpa using hc⟩

end EDa8

namespace EDa8
open EDa4
variable (p : ℕ) [Fact p.Prime]

theorem unit_i (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) :
    IsUnit (Section74b.red p xs ys (SectionA4o.qci 0 1)) := by
  rw [EDa6.red_qci p h2, isUnit_cm_iff]; simp

theorem unit_j (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) :
    IsUnit (Section74b.red p xs ys SectionA4o.qj) := by
  rw [EDa6.red_qj p h2]; exact isUnit_jm p xs ys hxy

theorem neg_one_ne_zero (h2 : (2 : ZMod p) ≠ 0) : (-1 : ZMod p) ≠ 0 := by
  intro h; apply h2
  have : (1 : ZMod p) = 0 := by simpa using h
  exact absurd this one_ne_zero

theorem g1_ne_one (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) :
    SectionA4e.rhoT p xs ys (SectionA4o.qci 0 1) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := rhoT_eq_one_smul p xs ys (unit_i p h2 xs ys) h
  rw [EDa6.red_qci p h2] at hc
  have := congrFun (congrFun hc 0) 0
  simp [cm] at this

theorem g2_ne_one (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) :
    SectionA4e.rhoT p xs ys SectionA4o.qj ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := rhoT_eq_one_smul p xs ys (unit_j p h2 xs ys hxy) h
  rw [EDa6.red_qj p h2] at hc
  have a := congrFun (congrFun hc 0) 0
  have b := congrFun (congrFun hc 1) 1
  simp [jm] at a b
  apply h2
  linear_combination a + b

theorem g1_ne_g2 (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) :
    SectionA4e.rhoT p xs ys (SectionA4o.qci 0 1) ≠ SectionA4e.rhoT p xs ys SectionA4o.qj := by
  intro h
  obtain ⟨c, hc⟩ := rhoT_eq_smul p xs ys (unit_i p h2 xs ys) (unit_j p h2 xs ys hxy) h
  rw [EDa6.red_qci p h2, EDa6.red_qj p h2] at hc
  have a := congrFun (congrFun hc 0) 0
  have b := congrFun (congrFun hc 0) 1
  have d := congrFun (congrFun hc 1) 0
  simp [jm, cm] at a b d
  have hx : xs = 0 := a
  have hy : ys = 0 := by
    have : (2 : ZMod p) * ys = 0 := by linear_combination b + d
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [hx, hy] at hxy
  apply neg_one_ne_zero p h2
  rw [← hxy]; ring

end EDa8
