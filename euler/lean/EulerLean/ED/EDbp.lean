import Stage83cut

/-! Exact identity for the mixed-parity count with a p-divisibility condition (p ≡ 3 mod 4, p ∣ m, m odd):
  b_p(2m) = 16 σ(m/p²) if p² ∣ m, and 0 otherwise.
Glue over existing lemmas (Section64.bp_eq, Section69.bp_zero / bp_card, Section70.hmix_of_hjac, Section80.hjac).
No change to HPrime or the existing chain. -/

namespace EDbp

theorem bp_exact {m p : ℕ} (hm : m % 2 = 1) (hp : p.Prime) (h3 : p % 4 = 3) (hpm : p ∣ m) :
    Section42.bp p (2 * m) = if p ^ 2 ∣ m then 16 * Section51.sig (m / p ^ 2) else 0 := by
  rw [Section64.bp_eq]
  have hpm2 : p ∣ 2 * m := Dvd.dvd.mul_left hpm 2
  have hcop : Nat.Coprime (p ^ 2) 2 := by
    apply Nat.Coprime.pow_left
    have hp2 : p ≠ 2 := by rintro rfl; omega
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  by_cases h2 : p ^ 2 ∣ m
  · rw [if_pos h2]
    obtain ⟨m', hm'⟩ := h2
    have hdvd : p ^ 2 ∣ 2 * m := Dvd.dvd.mul_left ⟨m', hm'⟩ 2
    have hodd' : m' % 2 = 1 := by
      rw [hm'] at hm
      exact Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hm)).2
    have hdiv : (2 * m) / p ^ 2 = 2 * m' := by
      rw [hm']
      have : 2 * (p ^ 2 * m') = p ^ 2 * (2 * m') := by ring
      rw [this]
      exact Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)
    have hdiv' : m / p ^ 2 = m' := by
      rw [hm']; exact Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)
    rw [Section69.bp_card hp h3 hdvd, hdiv, hdiv']
    exact Section70.hmix_of_hjac (fun k hk => Section80.hjac k hk) m' hodd'
  · rw [if_neg h2]
    have hn : ¬ p ^ 2 ∣ 2 * m := fun h => h2 (hcop.dvd_of_dvd_mul_left h)
    exact Section69.bp_zero hp h3 hpm2 hn

end EDbp

#print axioms EDbp.bp_exact
