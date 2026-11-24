import Stage83cut
import EDc0

/-!
# EDcDefs.lean   (PRODUCTION-FACING; UNTESTED until compiled)

Phase 8A/8B.  Generalised hypothesis DEFINITIONS for the Chebyshev (2.04) route, placed before every consumer so
that the module graph stays acyclic.  Imports `Stage83cut` (tracked, imports tracked `StageA4o`) and `EDc0`.
No `EDb8`, no `EDcert*`.

* `H31gt3A`, `H31ndvdA`, `H31A` : the A-shaped counterparts of `Section83.H31gt3`, `Section70.H31ndvd`,
  `Section65.H31`.  Only the divisor term `τ(m)√m` is replaced by `Amaj (51/50) m · √m`; everything else is
  verbatim.
* `HPrime204Restricted` : the relaxed prime-case spectral hypothesis (bound `(51/25)√l`, primes `l ≡ 3 mod 4`).
  It is a HYPOTHESIS (a `def : Prop`), not a theorem.  It is OPEN.
* `H31gt3A_of_H31gt3` : the original `H31gt3` implies the A-shaped one (uses `EDc0.tau_le_Amaj`).
  This is the only theorem here; the converse is NOT claimed.
-/

namespace EDcDefs

open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

/-- A-shaped `H31gt3`: `Section83.H31gt3` with `τ(m)` replaced by `Amaj (51/50) m`. -/
def H31gt3A : Prop := ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
  ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ m → p ≤ Section63b.Pn (2 * m) → 3 < p →
    (Section42.bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
      ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
        + EDc0.Amaj (51 / 50) m * Real.sqrt m / (3 * (Section51.sig m : ℝ))

/-- A-shaped `Section70.H31ndvd`. -/
def H31ndvdA : Prop := ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
  ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ m → p ≤ Section63b.Pn (2 * m) →
    (Section42.bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
      ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
        + (if 3 < p then EDc0.Amaj (51 / 50) m * Real.sqrt m / (3 * (Section51.sig m : ℝ)) else 0)

/-- A-shaped `Section65.H31`. -/
def H31A : Prop := ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
  ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ Section63b.Pn (2 * m) →
    (Section42.bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
      ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1))
        + (if 3 < p then EDc0.Amaj (51 / 50) m * Real.sqrt m / (3 * (Section51.sig m : ℝ)) else 0)

open Classical in
/-- The relaxed prime-case hypothesis: bound `(51/25) √l ‖f‖` (instead of `2 √l ‖f‖`), only for primes
`l ≡ 3 (mod 4)`.  OPEN; stated as a hypothesis only.  Same data `(p, xs, ys)` and same orthogonality
conditions as `EDb8.HPrime`. -/
def HPrime204Restricted : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_hp3 : p % 4 = 3) (_hp4 : 3 < p) (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1)
    (l : ℕ), l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ (51 / 25) * Real.sqrt l * ‖f‖

/-- The original `H31gt3` implies the A-shaped one, because `τ(m) ≤ Amaj (51/50) m`.
The converse is not claimed. -/
theorem H31gt3A_of_H31gt3 (h : Section83.H31gt3) : H31gt3A := by
  intro m hm2 hmq h64 p hp hp3 hpm hpP hp4
  have hm0 : m ≠ 0 := by omega
  have hsig : (0 : ℝ) < (Section51.sig m : ℝ) := by
    have : 0 < Section51.sig m := by
      show 0 < ArithmeticFunction.sigma 1 m
      rw [ArithmeticFunction.sigma_one_apply]
      exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd)
        ⟨1, Nat.one_mem_divisors.mpr hm0⟩
    exact_mod_cast this
  have ht : (Section51.tau m : ℝ) ≤ EDc0.Amaj (51 / 50) m :=
    EDc0.tau_le_Amaj (by norm_num) m hm0
  have e : (Section51.tau m : ℝ) * Real.sqrt m / (3 * (Section51.sig m : ℝ))
      ≤ EDc0.Amaj (51 / 50) m * Real.sqrt m / (3 * (Section51.sig m : ℝ)) := by
    first
      | (gcongr; done)
      | (gcongr; exact ht)
  exact le_trans (h m hm2 hmq h64 p hp hp3 hpm hpP hp4) (add_le_add le_rfl e)

end EDcDefs
#print axioms EDcDefs.H31gt3A_of_H31gt3
