import Mathlib

namespace EDa3

variable {G : Type*} [Group G]

/-- If j normalises C and j² ∈ C then closure(C ∪ {j}) ⊆ C ∪ C·j. -/
theorem closure_subset (C : Subgroup G) (j : G)
    (hN : ∀ c, c ∈ C ↔ j * c * j⁻¹ ∈ C) (hj2 : j * j ∈ C) :
    ∀ g ∈ Subgroup.closure ((C : Set G) ∪ {j}), g ∈ C ∨ g * j⁻¹ ∈ C := by
  have hjb : ∀ c ∈ C, j * c * j⁻¹ ∈ C := fun c hc => (hN c).1 hc
  have hjb' : ∀ c ∈ C, j⁻¹ * c * j ∈ C := by
    intro c hc
    exact (hN (j⁻¹ * c * j)).2 (by simpa [mul_assoc] using hc)
  have hj2' : j⁻¹ * j⁻¹ ∈ C := by
    have := C.inv_mem hj2
    simpa [mul_inv_rev] using this
  let H : Subgroup G :=
    { carrier := {g | g ∈ C ∨ g * j⁻¹ ∈ C}
      one_mem' := Or.inl C.one_mem
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (C.mul_mem ha hb)
        · right
          have : a * b * j⁻¹ = a * (b * j⁻¹) := by group
          rw [this]; exact C.mul_mem ha hb
        · right
          have : a * b * j⁻¹ = (a * j⁻¹) * (j * b * j⁻¹) := by group
          rw [this]; exact C.mul_mem ha (hjb b hb)
        · left
          have : a * b = (a * j⁻¹) * (j * (b * j⁻¹) * j⁻¹) * (j * j) := by group
          rw [this]
          exact C.mul_mem (C.mul_mem ha (hjb _ hb)) hj2
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl (C.inv_mem ha)
        · right
          have : a⁻¹ * j⁻¹ = (j⁻¹ * (a * j⁻¹)⁻¹ * j) * (j⁻¹ * j⁻¹) := by group
          rw [this]
          exact C.mul_mem (hjb' _ (C.inv_mem ha)) hj2' }
  have hle : Subgroup.closure ((C : Set G) ∪ {j}) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      right; simp
  intro g hg
  exact hle hg

/-- order bound: |closure(C ∪ {j})| ≤ 2|C| -/
theorem card_closure_le [Finite G] (C : Subgroup G) (j : G)
    (hN : ∀ c, c ∈ C ↔ j * c * j⁻¹ ∈ C) (hj2 : j * j ∈ C) :
    Nat.card (Subgroup.closure ((C : Set G) ∪ {j})) ≤ 2 * Nat.card C := by
  classical
  have hsub : ((Subgroup.closure ((C : Set G) ∪ {j}) : Subgroup G) : Set G) ⊆
      (C : Set G) ∪ (fun c => c * j) '' (C : Set G) := by
    intro g hg
    rcases closure_subset C j hN hj2 g hg with h | h
    · exact Or.inl h
    · right; exact ⟨g * j⁻¹, h, by simp⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (C : Set G) ((fun c => c * j) '' (C : Set G))
  have h3 : ((fun c => c * j) '' (C : Set G)).ncard ≤ (C : Set G).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have e1 : Nat.card (Subgroup.closure ((C : Set G) ∪ {j})) =
      ((Subgroup.closure ((C : Set G) ∪ {j}) : Subgroup G) : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  have e2 : Nat.card C = (C : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  omega

end EDa3
#print axioms EDa3.card_closure_le
