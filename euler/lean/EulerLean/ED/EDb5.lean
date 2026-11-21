import StageA4o
import EDa6
import EDa8
import EDb1

namespace EDb5
open EDa4 SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

include h2 in
/-- every class of an invertible a + bI lies in K_p -/
theorem cls_mem_Kp (a b : ZMod p) (h : a ^ 2 + b ^ 2 ≠ 0) : cls p a b h ∈ Kp p xs ys := by
  have hr : SectionA4e.rhoT p xs ys (qci a.val b.val) = cls p a b h := by
    have hu : IsUnit (Section74b.red p xs ys (qci a.val b.val)) := by
      rw [EDa6.red_qci p h2, isUnit_cm_iff]; simpa using h
    rw [SectionA4e.rhoT_of_unit p xs ys hu]
    unfold cls
    congr 1
    apply Units.ext
    simp [EDa6.red_qci p h2]
  rw [← hr]
  exact Subgroup.subset_closure (Or.inl ⟨a.val, b.val, rfl⟩)

include h2 hxy in
theorem rhoT_mem_of_cm (x : Quaternion ℚ) (hu : IsUnit (Section74b.red p xs ys x)) (a b : ZMod p)
    (hred : Section74b.red p xs ys x = cm p a b) : SectionA4e.rhoT p xs ys x ∈ Kp p xs ys := by
  have hab : a ^ 2 + b ^ 2 ≠ 0 := (isUnit_cm_iff p a b).1 (hred ▸ hu)
  have : SectionA4e.rhoT p xs ys x = cls p a b hab := by
    rw [SectionA4e.rhoT_of_unit p xs ys hu]
    unfold cls
    congr 1
    apply Units.ext
    simp [hred]
  rw [this]; exact cls_mem_Kp p h2 xs ys a b hab

include h2 hxy in
theorem rhoT_mem_of_cmj (x : Quaternion ℚ) (hu : IsUnit (Section74b.red p xs ys x)) (a b : ZMod p)
    (hred : Section74b.red p xs ys x = cm p a b * jm p xs ys) :
    SectionA4e.rhoT p xs ys x ∈ Kp p xs ys := by
  have hcm : IsUnit (cm p a b) := by
    have : IsUnit (cm p a b * jm p xs ys) := hred ▸ hu
    exact (IsUnit.mul_iff.1 this).1
  have hab : a ^ 2 + b ^ 2 ≠ 0 := (isUnit_cm_iff p a b).1 hcm
  have : SectionA4e.rhoT p xs ys x = cls p a b hab * jcls p xs ys hxy := by
    rw [SectionA4e.rhoT_of_unit p xs ys hu]
    unfold cls jcls
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Units.ext
    simp [hred]
  rw [this]
  exact (Kp p xs ys).mul_mem (cls_mem_Kp p h2 xs ys a b hab)
    (by rw [← EDa6.rhoT_qj p h2 xs ys hxy]; exact Subgroup.subset_closure (Or.inr rfl))

include h2 hxy in
/-- P2: if p divides a coordinate pair of α·(1+i) (integer coordinates z), then ρ(α) ∈ K_p -/
theorem rhoT_mem_of_pair {m : ℕ} (hm : ¬ p ∣ m) (α : Quaternion ℚ) (hα : α ∈ Section75a.Hn m)
    (z0 z1 z2 z3 : ℤ) (hz : α * qci 1 1 = ⟨(z0 : ℚ), (z1 : ℚ), (z2 : ℚ), (z3 : ℚ)⟩)
    (hdiv : ((p : ℤ) ∣ z0 ∧ (p : ℤ) ∣ z1) ∨ ((p : ℤ) ∣ z2 ∧ (p : ℤ) ∣ z3)) :
    SectionA4e.rhoT p xs ys α ∈ Kp p xs ys := by
  have hq : qci 1 1 ∈ Section75a.Hn (1 ^ 2 + 1 ^ 2) := qci_mem 1 1
  have hq' : Section71d.QH (qci 1 1) := hq.1
  have hu1 : IsUnit (Section74b.red p xs ys α) :=
    SectionA1.red_isUnit p h2 xs ys hxy hα.1 m hα.2 hm
  have hu2 : IsUnit (Section74b.red p xs ys (qci 1 1)) := by
    rw [EDa6.red_qci p h2, isUnit_cm_iff]
    intro h0
    apply h2
    have : (2 : ZMod p) = ((1 : ℕ) : ZMod p) ^ 2 + ((1 : ℕ) : ZMod p) ^ 2 := by push_cast; ring
    rw [this]; exact h0
  have hB : IsUnit (Section74b.red p xs ys (α * qci 1 1)) := by
    rw [Section74b.red_mul p h2 xs ys hxy hα.1 hq']; exact hu1.mul hu2
  have hmul : SectionA4e.rhoT p xs ys (α * qci 1 1)
      = SectionA4e.rhoT p xs ys α * SectionA4e.rhoT p xs ys (qci 1 1) :=
    SectionA4e.rhoT_mul p h2 xs ys hxy hα.1 hq' hu1 hu2
  have hgen : SectionA4e.rhoT p xs ys (qci 1 1) ∈ Kp p xs ys :=
    Subgroup.subset_closure (Or.inl ⟨1, 1, rfl⟩)
  have hredB : Section74b.red p xs ys (α * qci 1 1)
      = Section74a.psi xs ys (z0 : ZMod p) (z1 : ZMod p) (z2 : ZMod p) (z3 : ZMod p) := by
    unfold Section74b.red
    rw [hz]
    have cz_int : ∀ z : ℤ, Section74b.cz p (z : ℚ) = (z : ZMod p) := by
      intro z
      rw [Section74b.cz_eq p (z : ℚ) (2 * z) (by push_cast; ring)]
      push_cast
      field_simp
    simp only [cz_int]
  have hBK : SectionA4e.rhoT p xs ys (α * qci 1 1) ∈ Kp p xs ys := by
    rcases hdiv with ⟨d0, d1⟩ | ⟨d2, d3⟩
    · have e0 : (z0 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z0 p).2 d0
      have e1 : (z1 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z1 p).2 d1
      apply rhoT_mem_of_cmj p h2 xs ys hxy _ hB (z2 : ZMod p) (z3 : ZMod p)
      rw [hredB, e0, e1]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Section74a.psi, cm, jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · have e2 : (z2 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z2 p).2 d2
      have e3 : (z3 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z3 p).2 d3
      apply rhoT_mem_of_cm p h2 xs ys hxy _ hB (z0 : ZMod p) (z1 : ZMod p)
      rw [hredB, e2, e3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Section74a.psi, cm]
  have : SectionA4e.rhoT p xs ys α
      = SectionA4e.rhoT p xs ys (α * qci 1 1) * (SectionA4e.rhoT p xs ys (qci 1 1))⁻¹ := by
    rw [hmul]; group
  rw [this]
  exact (Kp p xs ys).mul_mem hBK ((Kp p xs ys).inv_mem hgen)

end EDb5
#print axioms EDb5.rhoT_mem_of_pair
