# Lemma ledger and branch map: Howe-Huffman-Kohlmeyer-Kruer, "Euler's 1747 conjecture" (hexagon:2611.00370v1)

Date: 2026-11-16. Written by Claude (Cowork). Scripts are in this folder. Nothing here is a proof unless the Status says LEAN.

Status words: **LEAN-KERNEL** (Lean, standard axioms only) | **LEAN-NATIVE** (Lean via native_decide, compiler-trusting) | **COMPUTED** (script reproduces it) | **READ** (I followed the argument by hand) | **OPEN** (not checked).
"Tested" means an instance test, not a proof of the general statement.

## 1. Every numbered statement

| # | Statement | Status | Evidence / file | Next step and feasibility |
|---|---|---|---|---|
| Thm 1.1 | every n = 2 mod 4 is a + b, a,b in A | LEAN conditional | Euler1747.lean: assembly from Prop 6.1 as a hypothesis (`AnalyticRange`) | Unconditional once `AnalyticRange` (Prop 6.1) is proved; Prop 3.1 supplies one input to that proof |
| Lemma 2.1 | reduce to n = 2m, m odd, all primes of m = 3 mod 4 | LEAN-KERNEL (inside Euler1747.lean, standard axioms + native_decide ax only because of the finite part) | `euler_1747_of_analytic_range` | done |
| (2.1) | R(n) = 24 sigma(m) (Jacobi) | COMPUTED (n < 6000, all tested m) | audit_prop31.py asserts it | LEAN: hard, many sessions. Plan in JACOBI_PLAN.md (Hurwitz route; step A written, untested) |
| (2.2) | \|Rmix\| = (2/3) R | LEAN-KERNEL | FourSquaresMixed.lean, axioms propext, Classical.choice, Quot.sound | done |
| (2.3) sufficiency | sum_p b_p < \|Rmix(n)\| implies n = a + b with a, b in A | LEAN-KERNEL: Sufficiency.sufficiency in Sufficiency23.lean, standard axioms only, GitHub elementary run #9 green. Proves ONLY the pigeonhole implication (prime = 3 mod 4 dividing x^2+y^2 divides both). Does not prove \|Rmix\| = (2/3)R (that is (2.2), FourSquaresMixed.lean), R = 24 sigma(m) (Jacobi, open), or any bound on sum b_p | Sufficiency23.lean | the hypothesis sum b_p < \|Rmix\| is what Prop 3.1, Lemma 4.2, Prop 6.1 must supply |
| Bridge (3.7)-(3.8) | one-vector bound <h,Th> <= B\|\|h\|\|^2 implies (T f)(y0) <= sigma mu + B(1-mu) | HAND-DERIVED; reproduces the paper's constants (mu/3 = 2/(p(p-1)), 8/24 = 1/3) | none | LEAN-KERNEL, FINITE ALGEBRA ONLY: EulerBridge.pointwise_of_quadform in Bridge.lean, GitHub elementary run green (user report, 2026-11-17; run number not recorded here). The quadratic-form bound hquad is an explicit HYPOTHESIS and is NOT proved; Lemma 3.2 and Prop 3.1 remain open. The T, sigma, O, f of the paper are not defined in Lean; the theorem is about an abstract finite type |
| Prop 3.1 | b_p/R <= 2/(p(p-1)) + [p>3] tau sqrt m / (3 sigma) | COMPUTED: 3,059 (m,p) cases, 0 violations, one equality case (m=7, p=3) | audit_prop31.py | LEAN: needs Hurwitz order + finite quotient + Lemma 3.2. Not feasible near-term |
| Lemma 3.2 | \|\|T_m\|\| <= tau(m) sqrt m on {1,chi}^perp | COMPUTED: 82 instances (22 + 60), 0 violations. m=1 is an EQUALITY (ratio exactly 1, trivial: T_1 = identity) and is listed separately, not counted in the worst ratio. Worst NONTRIVIAL ratios: 0.8752 (p=7, m=47), 0.9156 (p=11, m=31), 0.9764 (p=19, m=59), 0.9517 (p=23, m=53), 0.9820 (p=31, m=5; largest nontrivial ratio seen), all from a separate sweep of odd m <= 61 with p not dividing m, 0 violations (these sweeps overlap the 82 listed above in part; distinct-instance count not established); earlier p=3 partial run | audit_lemma32.py | General Lean proof OPEN: the full spectral bound needs Jacquet-Langlands and weight-two Ramanujan-Petersson (Deligne), neither in Mathlib. The two exceptional modes (T_m 1 = sigma(m) 1, T_m chi = (m/p) sigma(m) chi) are a finite-group statement that could be formalized separately. Hecke identification (3.5) and "exactly {1,chi}" are READ only. Another assistant reports seven exact checks at p=7; not reproduced or merged with our 22 |
| Lemma 4.1 | Nmix(t) <= 2(t+1) | LEAN-KERNEL (integer t): Section4.Nmix_le in Lemma41.lean, standard axioms only, GitHub elementary run #2 green; also COMPUTED for t in [0,4000] | Lemma41.lean, audit_lemma4.py | real-t reduction to floor not formalized |
| Lemma 4.2 | (1/R) sum_{p>P} b_p <= (4/3) M(n) [ ... ] | COMPUTED: 1,164 tests, 0 violations, worst lhs/rhs 0.442 | audit_lemma4.py | LEAN-KERNEL, CONDITIONAL: Lemma42.lean (Section42.bp_le_16: bp <= 16 M (n/(p*p)+1); bp_zero: bp = 0 when n < p*p; lemma42: the summed (4.1) over p with p*p <= n), standard axioms only, GitHub elementary run #12 (commit 19411d9). Axiom list does NOT show the hypotheses it takes: hr2 (two-square count r2(u) <= 4M for 1 <= u <= n in the box, not in Mathlib, not proved) and hR (R >= 12n, i.e. Jacobi, not proved) |
| Lemma 5.1 | tau m / sigma <= (23/10) m^(1/5); M(n) <= (11/5) n^(1/5) | COMPUTED: C1^5, C2^5 exact match with the paper's fractions | audit_numbers.py | FIRST BOUND LEAN-KERNEL: Section51.lemma51_first in Lemma51.lean: tau(m) m / sigma(m) <= (23/10) m^(1/5) for m > 0 with every prime divisor = 3 mod 4 (the Lemma 2.1 situation), tau and sigma = Mathlib's sigma 0 and sigma 1; standard axioms only, GitHub elementary run #14 (commit 90efc43). Proved via the multiplicative function F(m) = tau^5 m^4 / sigma^5 <= 183143120027364343/2849934139195392 (= C1^5; Section51.tau_sigma_pow5) and a real fifth root. SECOND BOUND M(n) <= (11/5) n^(1/5) NOT DONE: M(n) is not defined in any Lean file here; only its arithmetic (C2^5) is checked in Section6Arithmetic.lean. LocalFactors.lean (maximisation, run #5, #9) is used by the first bound |
| Lemma 5.2 (5.2) | count of p in P3, 3<p<=t, <= 2t/15 + 1 | LEAN-KERNEL: Section5.prime_count_bound in Lemma52.lean (15*count <= 2t+15), standard axioms only, GitHub elementary run #4 green; also COMPUTED up to 3e6 | Lemma52.lean, audit_numbers.py | (5.3), (5.4) still open |
| (5.3) | sum_{p>P} 1/p^2 <= 2/(15P) + 2/P^2 | LEAN-KERNEL: Section5.prime_tail in Lemma52.lean (discrete partial summation), standard axioms only, GitHub elementary run #8; also COMPUTED | Lemma52.lean, audit_numbers.py | done |
| (5.4) | 2 sum 1/(p(p-1)) < 21/50 | LEAN-KERNEL: Section5.five_four in Lemma52.lean (sum over primes p = 3 mod 4, 3 < p, in the paper's form, using prime_tail for the tail), standard axioms only, GitHub elementary run #9 green; arithmetic also COMPUTED (partial sum 0.20685 + tail 0.002825 < 0.21) | Lemma52.lean, audit_numbers.py | done |
| Prop 6.1 | n = 2m >= 64^4 implies n in A + A | COMPUTED: the rational upper bound from (6.1) and (6.2) is 21235493/33177600 < 2/3 (the paper replaces X-dependent terms by bounds valid for X >= 64); exact match; real-valued bound 0.6337 at X=64. The final arithmetic compiled in Section6Arithmetic.lean (GitHub, standard axioms) | audit_numbers.py | LEAN conditional on Prop 3.1 and (2.1) is feasible and is the useful next target (see 3) |
| Lemma 7.1 | eps_j = 1 iff 4j+1 in A | PARTLY LEAN: `goodB_iff` (Bool test = membership in A) is proved; the count 43 and last element 313 come from #eval and an independent sieve, not from a theorem | Euler1747.lean `goodB_iff`, `cands` | euler_finite only needs candidates in A, not list completeness |
| Prop 7.2 | every n = 2 mod 4, n < 64^4, is a+b with min <= 313 | LEAN-NATIVE | `euler_finite`, run on GitHub (10m49s) and on a Mac. Axiom list includes the native_decide axiom | a kernel-only version would need a faster certified checker |

## 2. Branch map: every place the proof splits into cases

| Where | Branch | What differs | Tested? |
|---|---|---|---|
| Lemma 2.1 | m has a prime factor = 1 mod 4 vs none | peel off g in A and induct (strong induction on m) | LEAN: yes, in euler_1747_of_analytic_range |
| Section 2 | each prime p in P3 | uses "-1 is a non-residue mod p" | READ |
| Prop 3.1 | p does not divide m | spectral estimate via T_m on Y_p | COMPUTED (all tested cases) |
| Prop 3.1 | p divides m, p^2 does not divide m | b_p = 0 exactly | COMPUTED: 349 cases, 0 failures |
| Prop 3.1 | p^2 divides m | b_p = 16 sigma(m/p^2) exactly, and b_p/R <= 2/(3 p^2) | COMPUTED: 106 and 596 cases, 0 failures |
| Prop 3.1 / (3.8) | p = 3 | mu_p = 1, second term vanishes, bound is 1/3 | COMPUTED: 345 cases, 0 failures; equality at m=7 |
| Prop 3.1 / (3.8) | p > 3 | extra term tau sqrt m / (3 sigma) | COMPUTED |
| Lemma 3.2 | one-dimensional automorphic reps vs the rest | 1-dim reps lie in span{1, chi_p}; the rest transfer by Jacquet-Langlands to weight 2 and are bounded by Deligne | tested only through the outcome (eigenvalues of T_m); the identification is READ and unverified. A second assistant's argument for "exactly {1, chi}" looks right to me but is unverified |
| Section 4 / Lemma 4.2 | prime p divides the first coordinate pair vs the second | factor 2 in 16 M(n)(n/p^2+1) | READ + COMPUTED through Lemma 4.2 |
| Lemma 5.1 | prime < 32 vs >= 32 | for >= 32 each local factor <= 1 because e+1 <= 2e <= p^(e/5) | COMPUTED: the table of maximizing e for the 6 primes in P3 and 4 primes = 1 mod 4 |
| Lemma 5.2 | the 8 residue classes mod 60 | S = {7,11,19,23,31,43,47,59}; p = 3 handled separately | COMPUTED up to 3e6 |
| Prop 6.1 | small primes p <= P = 2X vs large p > P | (6.1) vs (6.2), then add | COMPUTED: both parts and the sum |
| Prop 6.1 | the range X >= 64 | three numeric side bounds (4/9, 5/4, 1/64) | COMPUTED |
| Section 7 | n < 64^4 vs n >= 64^4 | finite certificate vs analytic | LEAN-NATIVE for the finite side |
| Section 7 | i <= k in the existence of (i, k-i) | the paper uses i <= k; an earlier note of mine wrongly said i < k | corrected |
| Proof of Thm 1.1 | 2m0 >= 64^4 vs less | Prop 6.1 vs Prop 7.2 | LEAN: in euler_1747_of_analytic_range |
| Theorem scope | only n = 2 mod 4 | other residues are not covered by this paper | n/a |

## 3. What "every lemma in Lean" can honestly mean

1. **Feasible, elementary, finite:** Lemma 4.1, (2.3) sufficiency, Lemma 5.1, Lemma 5.2 with (5.3) and (5.4), the final arithmetic of Prop 6.1, and the reduction statements. These are the bulk of the numbered items.
2. **Large but standard:** Jacobi's count (2.1) and the Hurwitz order is Euclidean (JACOBI_PLAN.md, steps A to C).
3. **Not possible today:** Lemma 3.2 and therefore Prop 3.1. They need the Jacquet-Langlands correspondence and Deligne's Ramanujan bound, neither of which is in Mathlib. This is the real boundary: no amount of formalizing sections 4 to 6 removes it.

**The sharpest honest target:** replace the single hypothesis `AnalyticRange` by the one input that is actually deep, Prop 3.1, taken as a hypothesis (together with (2.1)). Then formalize Lemma 4.1, 4.2, 5.1, 5.2 and Prop 6.1 around it. The Lean theorem would read: Euler's conjecture follows from Prop 3.1 and Jacobi's count. That shrinks the unproved part to the spectral estimate and makes everything else kernel-checked.
