import StageA4o

namespace EDa7
open SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

open Classical in
/-- if Γ ∩ K contains four distinct elements then 4 |O_K| ≤ |K| -/
theorem four_card_OK_le (K : Subgroup (SectionA2.PGL2 p)) (g : Fin 4 → SectionA2.PGL2 p)
    (hg : Function.Injective g)
    (hΓ : ∀ i, g i ∈ SectionA3b.Gam p h2 xs ys hxy) (hK : ∀ i, g i ∈ K) :
    4 * (OK p h2 xs ys hxy K).card ≤ Nat.card K := by
  let Kf : Finset (SectionA2.PGL2 p) := Finset.univ.filter (fun x => x ∈ K)
  have hKf : Kf.card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hmaps : ∀ x ∈ Kf, mkY p h2 xs ys hxy x ∈ OK p h2 xs ys hxy K := by
    intro x hx
    rw [mem_OK]
    exact ⟨x, by simpa [Kf] using hx, rfl⟩
  have hfib : ∀ y ∈ OK p h2 xs ys hxy K, 4 ≤ (Kf.filter (fun x => mkY p h2 xs ys hxy x = y)).card := by
    intro y hy
    obtain ⟨k0, hk0, rfl⟩ := (mem_OK p h2 xs ys hxy K _).1 hy
    have : (Finset.univ.image (fun i : Fin 4 => g i * k0)) ⊆
        Kf.filter (fun x => mkY p h2 xs ys hxy x = mkY p h2 xs ys hxy k0) := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp only [Finset.mem_filter, Kf, Finset.mem_univ, true_and]
      refine ⟨K.mul_mem (hK i) hk0, ?_⟩
      rw [mkY_eq_iff]
      simpa using hΓ i
    have hc : (Finset.univ.image (fun i : Fin 4 => g i * k0)).card = 4 := by
      rw [Finset.card_image_of_injective _ (fun a b h => hg (mul_right_cancel h))]
      simp
    calc 4 = _ := hc.symm
      _ ≤ _ := Finset.card_le_card this
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  calc 4 * (OK p h2 xs ys hxy K).card
      = ∑ y ∈ OK p h2 xs ys hxy K, 4 := by simp [mul_comm]
    _ ≤ ∑ y ∈ OK p h2 xs ys hxy K, (Kf.filter (fun x => mkY p h2 xs ys hxy x = y)).card :=
        Finset.sum_le_sum hfib
    _ = Kf.card := hsum.symm
    _ = Nat.card K := hKf

end EDa7
#print axioms EDa7.four_card_OK_le
