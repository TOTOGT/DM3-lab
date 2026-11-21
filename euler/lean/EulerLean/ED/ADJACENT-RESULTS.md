# Adjacent results from the Euler 1747 work — ledger for a separate paper

Saved 21 Nov 2026 (Pablo Nogueira Grossi, G6 LLC; computations and Lean by Claude Sonnet 5.5). **Not part of the Euler proof.** The Euler theorem is established in Lean only under the hypothesis `HPrime`, which is unproved; `H31ndvd` and `AggTarget` have not been established. Nothing here has been sent or published. No priority claim is made: the literature has not been checked (see §7).

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

## 2a. Theorem C (kernel-checked finite certificate)
For n ≡ 2 (mod 4) with n < 64⁴ = 16,777,216 (4,194,304 values) there are good a, b with a + b = n and min(a, b) ≤ 313. Lean: `EDcert.euler_finite_k` (`EDcert.lean`, line 25; commit 8373b16; hashes in the paper's source table). Method: `EDcert.good_of_sq_add_sq` (gcd(x,y)=1 and x²+y² odd ⇒ good; `EDcertCore.lean` line 21), the 43 candidates `candCert` (all good numbers ≤ 313, each a coprime odd-sum square pair), `chunkOk` over 256 chunks of width 65536 (`decide +kernel`), soundness `EDcert.chunk_sound` (line 139). Axioms: propext, Classical.choice, Quot.sound only (`logs/repro/axioms_EDcert_EDb9k.txt`); no `native_decide`. The original `EDb9.euler_1747_of_hprime` is unchanged and still lists `Euler1747.allOk_true._native.native_decide.ax_1_1`. The conditional theorem `EDb9k.euler_1747_of_hprime_k` has the explicit hypothesis `HPrime`. Independent corroboration (not part of the proof): `finite_check.py`, 0 uncovered of 4,194,304.

## 3. Identity (9) (elementary proof on paper, not in Lean; implementation checked by computation)
For p ∤ m (so p ∤ n): the events "p | x0,x1" and "p | x2,x3" are disjoint, and
  b_p(2m) = 2·Σ_{a odd, p²a ≤ 2m} r2(a)·r2(2m − p²a).
Proof: for p ∤ m the two events are disjoint (both would give p² | 2m); swapping the pairs is a bijection carrying one event onto the other, so b_p = 2·#{x : p | x0, x1}; (u,v,x2,x3) ↦ (pu,pv,x2,x3) is a bijection onto quadruples with p²(u²+v²)+x2²+x3² = 2m and odd pair sums; with a = u²+v², parity of u+v equals parity of a, w = 2m − p²a is odd, so the pair-sum conditions hold automatically exactly when a is odd; counting by r2(a)·r2(w) gives (9). The implementation was tested against brute-force enumeration of Rmix on 14 cases (`agg_ndvd.py A`, all equal). Derivation: x0=pu, x1=pv, u+v odd ⇔ a=u²+v² odd; w = n − p²a is then odd, and x2+x3 odd ⇔ w odd.

## 4. Local densities (checked by exact counts mod p^s)
Conditional density of "p | x0,x1" in Rmix: r_p(0) = 1/(p(p−1)) for p ∤ n; r_p(k) = (p^{k−1} − 1)/(p^{k+1} − 1) for k = v_p(m) ≥ 1. Same formula for p = 3 and p > 3. Definition: σ_p(n) = lim_s p^(−3s)·#{x mod p^s : Q(x) ≡ n (mod p^s)} with Q = x0²+x1²+x2²+x3² (the script computes counts at finite levels s and agreement with the predicted values was observed at every tested (p, s, k) = (3,4,1), (3,4,2), (3,5,3), (3,6,4), (7,3,1), (7,4,2), (11,3,1), (11,4,2), (19,3,1), (19,3,2); stabilization at a threshold such as s ≥ k+2 is not proved here); σ_p^c(n) is the same limit with the extra condition p | x0, p | x1; r_p = σ_p^c/σ_p. These are p-adic counts, not statements about integers; they bear on integer counts only through a Hardy–Littlewood/Siegel-type heuristic (integer points distributed among residue classes as the local counts predict), which is not proved here. Derivation: `AGG-PADIC.md`, checks: `local_density_check.py`. Consequence: b_p(2m)/(24σ(m)) ≈ (4/3)/(p(p−1)) for p ∤ m. Caveat: `local_density_check.py` covers k ≥ 1 only (30 cases, `logs/repro/local_density_check.log`); r_p(0) is derived but not covered by that exact-count check, and is tested only through the reduction in §3 and the runs in §6.

## 5. Observation D (numerical, UNPROVEN, found post-hoc)
For odd m with 3 ∤ m:

  b_3(2m) = (16/3)·(σ(m) − c(m)),   Σ c(n)qⁿ = η(6z)⁴ = q∏(1 − q^{6k})⁴ (c(n)=0 unless n ≡ 1 mod 6; the description of η(6z)⁴ as a weight-2, level-36 CM form is recorded in the header of `agg_p3_exact.py` and is unchecked against a source).

Found post hoc: in Part B the p=3 residual ρ was exactly zero for several fresh m (m = 10,000,799, 100,002,781, 1,000,000,787, 1,000,002,787; `logs/ndvd_B.log`), which prompted inspection of b₃(2m)/σ(m); no general condition for vanishing is claimed. Verified for all 200,000 odd m ≤ 600,000 with 3 ∤ m: zero exceptions (`agg_p3_exact.py`, log `logs/p3_exact_600k.log`; the relation was read off on the 1,333 odd m ≤ 4000 with 3 ∤ m; the other 198,667 values were not used to formulate it and all agree; c(m) ≠ 0 for 52,930 values). No derivation has been found; any theta-series or CM identification is unchecked and no literature search has been made.
Role in the Euler argument: none is needed. The p = 3 inequality b_3(2m) ≤ 8σ(m) for 3 ∤ m is already a Lean theorem, `Section83.bp3` (`Stage83cut.lean`; axioms propext, Classical.choice, Quot.sound; used in `Section83.h31ndvd_of`). Observation D would give the exact value in place of that inequality and is consistent with it: if it holds, b_3 ≤ 8σ(m) ⇔ c(m) ≥ −σ(m)/2, and the observed minimum of c(m)/σ(m) over m ≤ 600,000 is exactly −0.5 at m = 7 (equality: b_3(14) = 64 = 8σ(7)).

## 6. Numerical record
Bound (3) is the H31 inequality b_p(2m)/(24σ(m)) ≤ 2/(p(p−1)) + 1_{p>3}·τ(m)√m/(3σ(m)), for primes p ≡ 3 (mod 4) with p ≤ ⌊2(2m)^{1/4}⌋ (equation (3) of the separate paper).
Part A (p = 3, all odd m ≤ 600,000, 3 ∤ m): max b_3/(8σ) = 1.0000 (m = 7), then 0.8421 (37), 0.8235 (67); max over m ≥ 10⁴ is 0.6923; mean 0.6667 (main term 2/3); residual ρ = b_3/(24σ) − 2/9 within [−0.222, +0.111] (minimum −2/9 only at m = 1, where b_3(2) = 0; maximum +1/9 at m = 7, where b_3(14) = 64; both confirmed by direct enumeration; if Observation D holds, ρ = −2c(m)/(9σ(m)), so these are c/σ = 1 at m = 1 and −1/2 at m = 7), max |ρ| by decade: 0.222, 0.0444, 0.0209, 0.0085.
Part B (fresh m at 10⁷, 10⁸, 10⁹; p ∈ {3, 7, 11, 19, 23, 31, 43}; `logs/ndvd_B.log`): the main term (4/3)/(p(p−1)) frozen in the header of `agg_ndvd.py` (sha256 prefix c3726040116f) approximates all 60 observed counts, with residuals recorded separately in the log; the residual in m^{1/2} units, |ρ|·24σ(m)/√m = |b_p − 32σ(m)/(p(p−1))|/√m, has maximum 6.695 over the 51 pairs with p > 3 (maximum |ρ|/E = 0.418 with E = τ(m)√m/(3σ(m))) and 10.658 over the 9 pairs with p = 3, where the bound (3) has no allowance term; these are maxima over 60 tested pairs, not a uniform bound (the figures "about 11" and "0.67" in earlier notes pooled p = 3 with p > 3 and are superseded); every slack in H31ndvd is non-negative (b/bound between 0.66 and 0.70). The tests support the proposed estimate within the sampled range but establish no uniform error bound; this is evidence for an estimate, not a proof.

## 7. Before any publication
- Check the literature for Theorem A (scaling + Jacobi) and Observation D (quaternary forms x²+y²+9z²+9w², Liouville/Alaca–Williams-type formulas) before calling anything new. A Lean proof establishes the formal statement, not historical priority.
- A DOI/dated public record (e.g. Zenodo) shows when something was disclosed, not that it is original. Nothing is to be sent or posted until Pablo decides.
- Observation D stays labelled as an observation until proved.

## Files
`EDbp.lean`, `AGG-PADIC.md`, `agg_ndvd.py`, `agg_p3_exact.py`, `local_density_check.py`, `agg_scale_k.py`, `logs/ndvd_A.log`, `logs/ndvd_A600k.log`, `logs/ndvd_B.log`, `logs/p3_exact_600k.log` (all under `euler/lean/EulerLean/ED/`).
