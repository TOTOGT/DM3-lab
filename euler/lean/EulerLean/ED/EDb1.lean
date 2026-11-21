import StageA4o
import EDa6
import EDa8

namespace EDb1
open EDa4 SectionA4o
variable (p : ℕ) [Fact p.Prime]

theorem Kp_le (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) :
    Kp p xs ys ≤ Subgroup.closure ((Csub p : Set (PGL2 p)) ∪ {jcls p xs ys hxy}) := by
  unfold Kp
  apply Subgroup.closure_mono
  rintro g (⟨c, d, rfl⟩ | hg)
  · exact Or.inl (EDa6.rhoT_qci_mem p h2 xs ys c d)
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Or.inr (by simp [EDa6.rhoT_qj p h2 xs ys hxy])

/-- an element of K_p is in C_p or in C_p · ρ(j) -/
theorem Kp_cases (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (g : PGL2 p) (hg : g ∈ Kp p xs ys) : g ∈ Csub p ∨ g * (jcls p xs ys hxy)⁻¹ ∈ Csub p := by
  have hN : ∀ c, c ∈ Csub p ↔ jcls p xs ys hxy * c * (jcls p xs ys hxy)⁻¹ ∈ Csub p :=
    jcls_normalises p xs ys hxy
  have hj2 : jcls p xs ys hxy * jcls p xs ys hxy ∈ Csub p := by
    rw [jcls_sq p xs ys hxy]; exact (Csub p).one_mem
  exact EDa3.closure_subset (Csub p) (jcls p xs ys hxy) hN hj2 g (Kp_le p h2 xs ys hxy hg)

theorem sqodd (z : ℤ) : 1 ≤ (2 * z + 1) ^ 2 := by
  rcases le_or_gt 0 z with h | h
  · nlinarith
  · have : 2 * z + 1 ≤ -1 := by omega
    nlinarith

/-- the coordinates of a half-odd unit: cz of re and imJ are nonzero -/
theorem half_coords (h2 : (2 : ZMod p) ≠ 0) (x : Quaternion ℚ) (a b c d : ℤ)
    (ha : x.re = a + 1 / 2) (hb : x.imI = b + 1 / 2) (hc : x.imJ = c + 1 / 2) (hd : x.imK = d + 1 / 2)
    (hn : Quaternion.normSq x = 1) :
    Section74b.cz p x.re ≠ 0 ∧ Section74b.cz p x.imJ ≠ 0 := by
  have hn' : x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hn; exact hn
  rw [ha, hb, hc, hd] at hn'
  have e : ((2 * a + 1 : ℤ) : ℚ) ^ 2 + ((2 * b + 1 : ℤ) : ℚ) ^ 2 + ((2 * c + 1 : ℤ) : ℚ) ^ 2
      + ((2 * d + 1 : ℤ) : ℚ) ^ 2 = 4 := by push_cast; linarith
  have e' : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 + (2 * c + 1) ^ 2 + (2 * d + 1) ^ 2 = (4 : ℤ) := by
    exact_mod_cast e
  have p1 := sqodd a
  have p2 := sqodd b
  have p3 := sqodd c
  have p4 := sqodd d
  have q1 : (2 * a + 1) ^ 2 = 1 := by linarith
  have q3 : (2 * c + 1) ^ 2 = 1 := by linarith
  refine ⟨?_, ?_⟩
  · rw [Section74b.cz_eq p x.re (2 * a + 1) (by rw [ha]; push_cast; ring)]
    apply mul_ne_zero
    · intro h0
      have : ((2 * a + 1 : ℤ) : ZMod p) ^ 2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod p) q1
      rw [h0] at this; simp at this
    · exact inv_ne_zero h2
  · rw [Section74b.cz_eq p x.imJ (2 * c + 1) (by rw [hc]; push_cast; ring)]
    apply mul_ne_zero
    · intro h0
      have : ((2 * c + 1 : ℤ) : ZMod p) ^ 2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod p) q3
      rw [h0] at this; simp at this
    · exact inv_ne_zero h2

theorem half_unit_not_in_K (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (x : Quaternion ℚ) (a b c d : ℤ)
    (ha : x.re = a + 1 / 2) (hb : x.imI = b + 1 / 2) (hc : x.imJ = c + 1 / 2) (hd : x.imK = d + 1 / 2)
    (hn : Quaternion.normSq x = 1) (hx : IsUnit (Section74b.red p xs ys x)) :
    SectionA4e.rhoT p xs ys x ∉ Kp p xs ys := by
  intro hK
  obtain ⟨hA, hC⟩ := half_coords p h2 x a b c d ha hb hc hd hn
  set A := Section74b.cz p x.re
  set B := Section74b.cz p x.imI
  set C := Section74b.cz p x.imJ
  set D := Section74b.cz p x.imK
  have hred : Section74b.red p xs ys x = Section74a.psi xs ys A B C D := rfl
  rw [SectionA4e.rhoT_of_unit p xs ys hx] at hK
  rcases Kp_cases p h2 xs ys hxy _ hK with ⟨a', b', hab, hEq⟩ | ⟨a', b', hab, hEq⟩
  · -- case C_p
    have hEq' : (QuotientGroup.mk hx.unit : PGL2 p) = QuotientGroup.mk ((isUnit_cm_iff p a' b').2 hab).unit := hEq
    obtain ⟨l, hl⟩ := EDa8.mk_eq_smul p _ _ hEq'
    have hl' : cm p a' b' = l • Section74a.psi xs ys A B C D := by
      have := hl; simpa [hred] using this
    have hne : cm p a' b' ≠ 0 := ((isUnit_cm_iff p a' b').2 hab).ne_zero
    have hl0 : l ≠ 0 := by
      intro h0; apply hne; rw [hl', h0]; simp
    have e00 := congrFun (congrFun hl' 0) 0
    have e11 := congrFun (congrFun hl' 1) 1
    have e01 := congrFun (congrFun hl' 0) 1
    have e10 := congrFun (congrFun hl' 1) 0
    simp [cm, Section74a.psi] at e00 e11 e01 e10
    have s1 : l * (2 * (C * xs - D * ys)) = 0 := by linear_combination e11 - e00
    have s2 : l * (2 * (C * ys + D * xs)) = 0 := by linear_combination -(e01 + e10)
    have t1 : C * xs - D * ys = 0 := by
      have := (mul_eq_zero.1 s1).resolve_left hl0
      exact (mul_eq_zero.1 this).resolve_left h2
    have t2 : C * ys + D * xs = 0 := by
      have := (mul_eq_zero.1 s2).resolve_left hl0
      exact (mul_eq_zero.1 this).resolve_left h2
    apply hC
    have : C * (xs ^ 2 + ys ^ 2) = 0 := by linear_combination xs * t1 + ys * t2
    rw [hxy] at this
    linear_combination -this
  · -- case C_p · ρ(j)
    have hjinv : (jcls p xs ys hxy)⁻¹ = jcls p xs ys hxy :=
      inv_eq_of_mul_eq_one_right (jcls_sq p xs ys hxy)
    rw [hjinv] at hEq
    have hg : (QuotientGroup.mk hx.unit : PGL2 p) =
        QuotientGroup.mk (((isUnit_cm_iff p a' b').2 hab).unit * (isUnit_jm p xs ys hxy).unit) := by
      have h1 : (QuotientGroup.mk hx.unit : PGL2 p) * jcls p xs ys hxy =
          cls p a' b' hab := hEq
      have h2' : (QuotientGroup.mk hx.unit : PGL2 p) =
          cls p a' b' hab * jcls p xs ys hxy := by
        rw [← h1, mul_assoc, jcls_sq p xs ys hxy, mul_one]
      rw [h2']
      unfold cls jcls
      rw [← QuotientGroup.mk_mul]
    obtain ⟨l, hl⟩ := EDa8.mk_eq_smul p _ _ hg
    have hl' : cm p a' b' * jm p xs ys = l • Section74a.psi xs ys A B C D := by
      have := hl; simpa [hred] using this
    have hne : cm p a' b' * jm p xs ys ≠ 0 :=
      (((isUnit_cm_iff p a' b').2 hab).mul (isUnit_jm p xs ys hxy)).ne_zero
    have hl0 : l ≠ 0 := by
      intro h0; apply hne; rw [hl', h0]; simp
    have e00 := congrFun (congrFun hl' 0) 0
    have e11 := congrFun (congrFun hl' 1) 1
    simp [cm, jm, Matrix.mul_apply, Fin.sum_univ_two, Section74a.psi] at e00 e11
    have s : l * (2 * A) = 0 := by linear_combination -(e00 + e11)
    have := (mul_eq_zero.1 s).resolve_left hl0
    exact hA ((mul_eq_zero.1 this).resolve_left h2)

end EDb1
#print axioms EDb1.half_unit_not_in_K
