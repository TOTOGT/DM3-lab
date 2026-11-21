import Stage83cut
import EDa6
import EDb4
import EDb5
import EDb6

namespace EDb7
open EDa4 SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

open Classical in
include h2 hxy in
/-- JOIN: b_p(2m) ≤ #{α ∈ Q_m : ρ(α) ∈ K_p}, via α = x·(1+i)⁻¹ (P1) and P2. -/
theorem bp_le_S {m : ℕ} (hm : ¬ p ∣ m) :
    Section42.bp p (2 * m) ≤ ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card) := by
  unfold Section42.bp
  have memHf : ∀ x, x ∈ (Section77a.Hn_finite m).toFinset ↔ x ∈ Section75a.Hn m :=
    fun x => Set.Finite.mem_toFinset _
  refine Finset.card_le_card_of_injOn EDb6.alphaOf ?_ ?_
  · intro x hx
    obtain ⟨hxR, hdiv⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
    obtain ⟨_, h01, h23, hsq⟩ := Section42.mem_Rmix.1 hxR
    have hmem : EDb6.alphaOf x ∈ Section75a.Hn m := EDb6.alpha_mem m x h01 h23 (by exact_mod_cast hsq)
    exact Finset.mem_filter.2 ⟨(memHf _).2 hmem,
      EDb5.rhoT_mem_of_pair p h2 xs ys hxy hm _ hmem (x 0) (x 1) (x 2) (x 3) (EDb6.alpha_mul x) hdiv⟩
  · intro x _ y _ hxy'
    exact EDb6.alpha_inj hxy'

end EDb7
#print axioms EDb7.bp_le_S
