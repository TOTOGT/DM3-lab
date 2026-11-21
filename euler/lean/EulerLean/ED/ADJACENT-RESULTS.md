# Adjacent results from the Euler 1747 work — ledger for a separate paper

Saved 21 Nov 2026 (Pablo Nogueira Grossi, G6 LLC; computations and Lean by Claude Sonnet 5.5). **Not part of the Euler proof.** `HPrime`, `H31ndvd`, `AggTarget` and the Euler theorem stay conditional. Nothing here has been sent or published. No priority claim is made: the literature has not been checked (see §7).

Notation: n = 2m, m odd, p prime ≡ 3 mod 4. Rmix(n) = {x ∈ Z⁴ : Σx² = n, x0+x1 odd, x2+x3 odd}. b_p(n) = #{x ∈ Rmix(n) : (p|x0 and p|x1) or (p|x2 and p|x3)}. σ = sum of divisors, τ = number of divisors, r2 = number of representations as a sum of two squares.

## 1. Theorem A (kernel-checked in Lean)
For m odd, p prime, p ≡ 3 mod 4, p | m:

  b_p(2m) = 16·σ(m/p²) if p² | m, and 0 otherwise.

Lean: `EDbp.bp_exact` in `euler/lean/EulerLean/ED/EDbp.lean` (commit 93ea1bb); axioms: propext, Classical.choice, Quot.sound only.
Statement as compiled: `theorem bp_exact {m p : ℕ} (hm : m % 2 = 1) (hp : p.Prime) (h3 : p % 4 = 3) (hpm : p ∣ m) : Section42.bp p (2 * m) = if p ^ 2 ∣ m then 16 * Section51.sig (m / p ^ 2) else 0`.
`Section42.bp p n` = card of `{x ∈ Rmix n | (p ∣ x0 ∧ p ∣ x1) ∨ (p ∣ x2 ∧ p ∣ x3)}` (equal to `Sufficiency.bp` by `Section64.bp_eq`).
Conventional proof. If p | x0, x1 and p | n then p | x2²+x3², and −1 is a non-residue mod p, so p | x2, x3 (symmetrically for the other disjunct). Hence b_p = #{x ∈ Rmix(n) : p | every coordinate}. Writing x = py gives Q(y) = n/p², which needs p² | 2m, i.e. p² | m; parity is preserved since p is odd. So b_p(2m) = |Rmix(2m/p²)| = 16σ(m/p²) by Lemma B, and b_p = 0 if p² ∤ m.
Honest status: a scaling argument plus Jacobi's four-square theorem. Its value is the exact form and the kernel-checked chain, not depth. Novelty unverified.

## 2. Lemma B (kernel-checked in Lean)
For m odd: |Rmix(2m)| = 16σ(m) = (2/3)·r4(2m), r4(2m) = 24σ(m) (Jacobi). Lean: `Section80.hjac` (Jacobi, odd m), `Section70.hmix_of_hjac`, `FourSq.mixed_count` (the 2/3 fraction). Same axiom check as the existing chain.

## 3. Lemma C (checked by computation, not in Lean)
For p ∤ m (so p ∤ n): the events "p | x0,x1" and "p | x2,x3" are disjoint, and
  b_p(2m) = 2·Σ_{a odd, p²a ≤ 2m} r2(a)·r2(2m − p²a).
Checked against brute-force enumeration of Rmix on 14 cases (`agg_ndvd.py A`, all equal). Derivation: x0=pu, x1=pv, u+v odd ⇔ a=u²+v² odd; w = n − p²a is then odd, and x2+x3 odd ⇔ w odd.

## 4. Local densities (checked by exact counts mod p^s)
Conditional density of "p | x0,x1" in Rmix: r_p(0) = 1/(p(p−1)) for p ∤ n; r_p(k) = (p^{k−1} − 1)/(p^{k+1} − 1) for k = v_p(m) ≥ 1. Same formula for p = 3 and p > 3. Derivation: `AGG-PADIC.md`, checks: `local_density_check.py`. Consequence: b_p(2m)/(24σ(m)) ≈ (4/3)/(p(p−1)) for p ∤ m.

## 5. Observation D (numerical, UNPROVEN, found post-hoc)
For odd m with 3 ∤ m:

  b_3(2m) = (16/3)·(σ(m) − c(m)),   Σ c(n)qⁿ = η(6z)⁴ = q∏(1 − q^{6k})⁴ (weight 2, level 36, CM by Q(√−3); c(n)=0 unless n ≡ 1 mod 6).

Found by inspection after Part B showed the p=3 residual vanishing exactly when m has a prime factor ≡ 2 mod 3 to an odd power. Verified for all 200,000 odd m ≤ 600,000 with 3 ∤ m: zero exceptions (`agg_p3_exact.py`, log `logs/p3_exact_600k.log`; the relation was first seen on m ≤ 4000 and the larger range was tested after). Plausibly a classical theta-series identity (θ(z)²θ(9z)² in M₂(Γ₀(36)), with a parity twist); not derived here, literature not checked.
Consequence for H31ndvd at p = 3 (its bound there has no error term): b_3 ≤ 8σ(m) ⇔ c(m) ≥ −σ(m)/2. Observed min of c(m)/σ(m) over m ≤ 600,000 is exactly −0.5 at m = 7 (equality: b_3(14) = 64 = 8σ(7)); elsewhere larger. If Observation D were proved, the p = 3 case would reduce to a bound |c(m)| ≤ τ(m)√m (Hecke/Deligne for a CM form) plus a finite check. That is conditional and not done.

## 6. Numerical record
Part A (p = 3, all odd m ≤ 600,000, 3 ∤ m): max b_3/(8σ) = 1.0000 (m = 7), then 0.8421 (37), 0.8235 (67); max over m ≥ 10⁴ is 0.6923; mean 0.6667 (main term 2/3); residual ρ = b_3/(24σ) − 2/9 within [−0.222, +0.111], max |ρ| by decade: 0.222, 0.0444, 0.0209, 0.0085.
Part B (fresh m at 10⁷, 10⁸, 10⁹; p ∈ {3, 7, 11, 19, 23, 31, 43}; `logs/ndvd_B.log`): the main term (4/3)/(p(p−1)) frozen in the header of `agg_ndvd.py` (sha256 prefix c3726040116f) predicts every count; for p > 3 the signed residual stays below about 11 in m^{1/2} units and below 0.67 of the allowance τ√m/(3σ); every slack in H31ndvd is non-negative (b/bound between 0.66 and 0.70). This is evidence for an estimate, not a proof.

## 7. Before any publication
- Check the literature for Theorem A (scaling + Jacobi) and Observation D (quaternary forms x²+y²+9z²+9w², Liouville/Alaca–Williams-type formulas) before calling anything new. A Lean proof establishes the formal statement, not historical priority.
- A DOI/dated public record (e.g. Zenodo) shows when something was disclosed, not that it is original. Nothing is to be sent or posted until Pablo decides.
- Observation D stays labelled as an observation until proved.

## Files
`EDbp.lean`, `AGG-PADIC.md`, `agg_ndvd.py`, `agg_p3_exact.py`, `local_density_check.py`, `agg_scale_k.py`, `logs/ndvd_A.log`, `logs/ndvd_A600k.log`, `logs/ndvd_B.log`, `logs/p3_exact_600k.log` (all under `euler/lean/EulerLean/ED/`).
