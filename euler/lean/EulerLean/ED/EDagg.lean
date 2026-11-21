import Stage83cut

namespace EDagg
open Section5 Section61 Section63b Section42

/-- Budget for the small-prime half of Prop 6.1, read from `Section63b.prop61_core`:
`2/3 - L(n)` where `L` is the large-prime bound of `Section63b.large_primes` evaluated at `u = n^(1/20)`
and `P = Pn n`, exactly as in `Section63.final_arith`. -/
noncomputable def largePrimeBound (n P : ℕ) : ℝ :=
  (4 / 3) * ((11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) *
    (2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ))

/-- The aggregate statement: the small-prime sum used by Prop 6.1, with the hypotheses and prime range
of `prop61_core` (primes `p ≡ 3 mod 4`, `p ≤ Pn (2m)`), bounded by `T`. No per-prime bound is assumed. -/
noncomputable def AggSmall (m : ℕ) (T : ℝ) : Prop :=
  (1 / (24 * (Section51.sig m : ℝ))) * ∑ p ∈ PT (Pn (2 * m)), (bp p (2 * m) : ℝ) ≤ T

/-- Aggregate target for Prop 6.1: the small-prime sum is below `2/3 - L(2m)`. -/
noncomputable def AggTarget (m : ℕ) : Prop :=
  AggSmall m (2 / 3 - largePrimeBound (2 * m) (Pn (2 * m)))

/-- Sanity link to the existing chain: the per-prime hypothesis of `prop61_core` (with error term `E`) implies
the aggregate bound `21/50 + E (2P/15 + 1)`.  This is `small_primes_sum` itself. -/
theorem agg_of_h31 (m : ℕ) (E : ℝ) (hR : 0 < 24 * (Section51.sig m : ℝ)) (hE : 0 ≤ E)
    (h31 : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ≤ Pn (2 * m) →
      (bp p (2 * m) : ℝ) / (24 * (Section51.sig m : ℝ))
        ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) + (if 3 < p then E else 0)) :
    AggSmall m (21 / 50 + E * (2 * (Pn (2 * m) : ℝ) / 15 + 1)) :=
  small_primes_sum (fun p => (bp p (2 * m) : ℝ)) (Pn (2 * m)) (24 * (Section51.sig m : ℝ)) E hR hE h31

end EDagg
#print axioms EDagg.agg_of_h31
