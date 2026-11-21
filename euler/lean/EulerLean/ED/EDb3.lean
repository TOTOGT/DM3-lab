import StageA4o
import EDa6
import EDa8
import EDb1
import EDb2

namespace EDb3
open EDa4 SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem HurU_coe_mem (u : SectionA3a2.HurU) :
    Section71d.QH ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) ∧
      Quaternion.normSq ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) = 1 :=
  (SectionA3a2.mem_iff _).1 u.2

include h2 hxy in
theorem red_unit_of_Hn {m : ℕ} (hm : ¬ p ∣ m) {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn m) :
    IsUnit (Section74b.red p xs ys x) :=
  SectionA1.red_isUnit p h2 xs ys hxy hx.1 m hx.2 hm

include h2 hxy in
theorem mul_mem_Hn {m : ℕ} (u : SectionA3a2.HurU) {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn m) :
    ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x ∈ Section75a.Hn m := by
  obtain ⟨hq, hn⟩ := HurU_coe_mem u
  refine ⟨Section71d.QH_mul hq hx.1, ?_⟩
  rw [map_mul, hn, one_mul]; exact hx.2

include h2 hxy in
theorem rhoT_unit_mul {m : ℕ} (hm : ¬ p ∣ m) (u : SectionA3a2.HurU) {x : Quaternion ℚ}
    (hx : x ∈ Section75a.Hn m) :
    SectionA4e.rhoT p xs ys (((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x)
      = SectionA4e.rhoT p xs ys ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * SectionA4e.rhoT p xs ys x := by
  obtain ⟨hq, hn⟩ := HurU_coe_mem u
  have hu1 : IsUnit (Section74b.red p xs ys ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ)) :=
    SectionA1.red_isUnit p h2 xs ys hxy hq 1 (by simpa using hn) (SectionA3a.not_dvd_one_p p)
  exact SectionA4e.rhoT_mul p h2 xs ys hxy hq hx.1 hu1 (red_unit_of_Hn p h2 xs ys hxy hm hx)

include h2 hxy in
theorem rhoT_unit_mem_Gam (u : SectionA3a2.HurU) :
    SectionA4e.rhoT p xs ys ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) ∈ SectionA3b.Gam p h2 xs ys hxy := by
  obtain ⟨hq, hn⟩ := HurU_coe_mem u
  exact SectionA4h.rhoT_unit_mem p h2 xs ys hxy ⟨hq, by simpa using hn⟩

open Classical in
noncomputable def Int8_img (x0 : Quaternion ℚ) : Finset (Quaternion ℚ) :=
  EDb2.Int8.image (fun w => w * x0)

open Classical in
include h2 hxy in
/-- P3: 3 · #{α ∈ Q_m : ρ(α) ∈ K_p} ≤ #{α ∈ Q_m : Γ ρ(α) ∈ O_p} -/
theorem three_mul_le {m : ℕ} (hm : ¬ p ∣ m) :
    3 * (((Section77a.Hn_finite m).toFinset).filter
          (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card
      ≤ (((Section77a.Hn_finite m).toFinset).filter
          (fun x => SectionA4o.mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x)
            ∈ OK p h2 xs ys hxy (Kp p xs ys))).card := by
  set Hf := (Section77a.Hn_finite m).toFinset with hHf
  set S := Hf.filter (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys) with hS
  set T := Hf.filter (fun x => SectionA4o.mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x)
            ∈ OK p h2 xs ys hxy (Kp p xs ys)) with hT
  have memHf : ∀ x, x ∈ Hf ↔ x ∈ Section75a.Hn m := fun x => Set.Finite.mem_toFinset _
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hfin : Finite SectionA3a2.HurU := Nat.finite_of_card_ne_zero (by rw [SectionA3a3.card_HurU]; norm_num)
  haveI := Fintype.ofFinite SectionA3a2.HurU
  let r : Quaternion ℚ → Quaternion ℚ → Prop :=
    fun x y => ∃ u : SectionA3a2.HurU, ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x = y
  have key := Finset.card_mul_le_card_mul r (s := S) (t := T) (m := 24) (n := 8) ?_ ?_
  · omega
  · -- every x in S is related to 24 elements of T
    intro x hx
    rw [hS, Finset.mem_filter, memHf] at hx
    obtain ⟨hxH, hxK⟩ := hx
    have hx0 : x ≠ 0 := by
      intro h0; have := hxH.2; rw [h0] at this; simp at this
      exact hm0 (by exact_mod_cast this.symm)
    have hsub : (Finset.univ.image (fun u : SectionA3a2.HurU => ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x))
        ⊆ T.bipartiteAbove r x := by
      intro y hy
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hy
      rw [Finset.mem_bipartiteAbove, hT, Finset.mem_filter, memHf]
      refine ⟨⟨mul_mem_Hn p h2 xs ys hxy u hxH, ?_⟩, ⟨u, rfl⟩⟩
      have eq : SectionA4o.mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ)
            * SectionA4e.rhoT p xs ys x) = SectionA4o.mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x) := by
        rw [SectionA4o.mkY_eq_iff]
        simpa using rhoT_unit_mem_Gam p h2 xs ys hxy u
      rw [rhoT_unit_mul p h2 xs ys hxy hm u hxH, eq, SectionA4o.mem_OK]
      exact ⟨_, hxK, rfl⟩
    have hinj : Function.Injective
        (fun u : SectionA3a2.HurU => ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x) := by
      intro u u' h
      have := mul_right_cancel₀ hx0 h
      exact Subtype.ext (Units.ext this)
    calc 24 = (Finset.univ.image (fun u : SectionA3a2.HurU => ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x)).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
            SectionA3a3.card_HurU]
      _ ≤ _ := Finset.card_le_card hsub
  · -- every y in T is related to at most 8 elements of S
    intro y hy
    by_cases hne : (S.bipartiteBelow r y).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      rw [Finset.mem_bipartiteBelow, hS, Finset.mem_filter, memHf] at hx0
      obtain ⟨⟨hx0H, hx0K⟩, u0, hu0⟩ := hx0
      have hsub : S.bipartiteBelow r y ⊆ Int8_img x0 := by
        intro x hx
        rw [Finset.mem_bipartiteBelow, hS, Finset.mem_filter, memHf] at hx
        obtain ⟨⟨hxH, hxK⟩, u, hu⟩ := hx
        set w : SectionA3a2.HurU := u⁻¹ * u0 with hw
        have hwx : ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ) * x0 = x := by
          have e1 : ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ)
              = (((u⁻¹ : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ)
                * ((u0 : (Quaternion ℚ)ˣ) : Quaternion ℚ) := rfl
          have e2 : (((u⁻¹ : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ)
                * ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) = 1 := by
            have : ((u⁻¹ * u : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) = 1 := by simp
            simpa using congrArg (fun z : (Quaternion ℚ)ˣ => (z : Quaternion ℚ)) this
          rw [e1, mul_assoc, hu0, ← hu, ← mul_assoc, e2, one_mul]
        have hρ : SectionA4e.rhoT p xs ys x
            = SectionA4e.rhoT p xs ys ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ) * SectionA4e.rhoT p xs ys x0 := by
          conv_lhs => rw [← hwx]
          exact rhoT_unit_mul p h2 xs ys hxy hm w hx0H
        have hwK : SectionA4e.rhoT p xs ys ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ) ∈ Kp p xs ys := by
          have : SectionA4e.rhoT p xs ys ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ)
              = SectionA4e.rhoT p xs ys x * (SectionA4e.rhoT p xs ys x0)⁻¹ := by
            rw [hρ]; group
          rw [this]; exact (Kp p xs ys).mul_mem hxK ((Kp p xs ys).inv_mem hx0K)
        obtain ⟨hq, hn⟩ := HurU_coe_mem w
        have hint := EDb2.unit_in_K p h2 xs ys hxy _ hq hn hwK
        unfold Int8_img
        rw [Finset.mem_image]
        exact ⟨_, hint, hwx⟩
      calc (S.bipartiteBelow r y).card ≤ (Int8_img x0).card := Finset.card_le_card hsub
        _ ≤ EDb2.Int8.card := Finset.card_image_le
        _ ≤ 8 := EDb2.Int8_card
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp

end EDb3
#print axioms EDb3.three_mul_le
