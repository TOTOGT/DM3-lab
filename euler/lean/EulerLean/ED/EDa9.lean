import StageA4o
import EDa6
import EDa7
import EDa8

namespace EDa9
open EDa4 SectionA4o
variable (p : ℕ) [Fact p.Prime]

theorem inj4 {α : Type*} (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> first
    | exact absurd h hab | exact absurd h.symm hab | exact absurd h hac | exact absurd h.symm hac
    | exact absurd h had | exact absurd h.symm had | exact absurd h hbc | exact absurd h.symm hbc
    | exact absurd h hbd | exact absurd h.symm hbd | exact absurd h hcd | exact absurd h.symm hcd

theorem mem4 {G : Type*} [Group G] (S : Subgroup G) (a b : G) (ha : a ∈ S) (hb : b ∈ S) :
    ∀ i, (![1, a, b, a * b] : Fin 4 → G) i ∈ S := by
  intro i
  fin_cases i
  · exact S.one_mem
  · exact ha
  · exact hb
  · exact S.mul_mem ha hb

theorem qci01_mem : qci 0 1 ∈ Section75a.Hn 1 := by
  simpa using qci_mem 0 1

theorem qj_mem : qj ∈ Section75a.Hn 1 := by
  refine ⟨Or.inl ⟨0, 0, 1, 0, by simp [qj], by simp [qj], by simp [qj], by simp [qj]⟩, ?_⟩
  simp [qj, Quaternion.normSq_def']

open Classical in
/-- |O_p| ≤ (p+1)/2, i.e. 2|O_p| ≤ p + 1, for the paper's K_p -/
theorem card_OK_Kp_le (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) :
    2 * (OK p h2 xs ys hxy (Kp p xs ys)).card ≤ p + 1 := by
  set g1 := SectionA4e.rhoT p xs ys (qci 0 1) with hg1
  set g2 := SectionA4e.rhoT p xs ys qj with hg2
  have hg2sq : g2 * g2 = 1 := by
    rw [hg2, EDa6.rhoT_qj p h2 xs ys hxy]; exact jcls_sq p xs ys hxy
  have n1 : g1 ≠ 1 := EDa8.g1_ne_one p h2 xs ys
  have n2 : g2 ≠ 1 := EDa8.g2_ne_one p h2 xs ys hxy
  have n3 : g1 ≠ g2 := EDa8.g1_ne_g2 p h2 xs ys hxy
  have n4 : g1 * g2 ≠ 1 := by
    intro h
    apply n3
    have : g1 = g2⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hg2sq)
  have n5 : g1 * g2 ≠ g1 := by
    intro h; apply n2; simpa using h
  have n6 : g1 * g2 ≠ g2 := by
    intro h; apply n1; simpa using h
  have mΓ1 : g1 ∈ SectionA3b.Gam p h2 xs ys hxy := SectionA4h.rhoT_unit_mem p h2 xs ys hxy (qci01_mem)
  have mΓ2 : g2 ∈ SectionA3b.Gam p h2 xs ys hxy := SectionA4h.rhoT_unit_mem p h2 xs ys hxy (qj_mem)
  have mK1 : g1 ∈ Kp p xs ys := Subgroup.subset_closure (Or.inl ⟨0, 1, rfl⟩)
  have mK2 : g2 ∈ Kp p xs ys := Subgroup.subset_closure (Or.inr rfl)
  let g : Fin 4 → SectionA2.PGL2 p := ![1, g1, g2, g1 * g2]
  have hg : Function.Injective g :=
    inj4 1 g1 g2 (g1 * g2) n1.symm n2.symm n4.symm n3 n5.symm n6.symm
  have hΓ : ∀ i, g i ∈ SectionA3b.Gam p h2 xs ys hxy := mem4 _ g1 g2 mΓ1 mΓ2
  have hK : ∀ i, g i ∈ Kp p xs ys := mem4 _ g1 g2 mK1 mK2
  have h4 := EDa7.four_card_OK_le p h2 xs ys hxy (Kp p xs ys) g hg hΓ hK
  have hK2 := EDa6.card_Kp_le p h2 xs ys hxy
  omega

end EDa9
#print axioms EDa9.card_OK_Kp_le
