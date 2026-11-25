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
| Bridge (3.7)-(3.8) | one-vector bound <h,Th> <= B\|\|h\|\|^2 implies (T f)(y0) <= sigma mu + B(1-mu) | HAND-DERIVED; reproduces the paper's constants (mu/3 = 2/(p(p-1)), 8/24 = 1/3) | none | LEAN-KERNEL, FINITE ALGEBRA ONLY: EulerBridge.pointwise_of_quadform in Bridge.lean, GitHub elementary run #17 (commit 89f925e, 2026-11-17): 'EulerBridge.pointwise_of_quadform' depends on axioms: [propext, Classical.choice, Quot.sound]. The quadratic-form bound hquad is an explicit HYPOTHESIS and is NOT proved; Lemma 3.2 and Prop 3.1 remain open. The T, sigma, O, f of the paper are not defined in Lean; the theorem is about an abstract finite type |
| Prop 6.1 stage 1 (small-prime sum) | (1/R) sum_{p in P3, p<=P} b_p <= 21/50 + E (2P/15 + 1) | HAND-DERIVED from (6.1) | none | LEAN-KERNEL, CONDITIONAL: Section61.small_primes_sum in Stage61a.lean (Lemma52.lean verbatim + new theorem), run #17 (re-confirmed in run #19), standard axioms only. b is an ABSTRACT count and Prop 3.1 for p <= P is the hypothesis h31, NOT proved (Lemma 3.2 open); uses (5.4) five_four and (5.2) prime_count_bound |
| Prop 6.1 stage 2b (large primes) | (1/R) sum_{p>P} b_p <= (4/3) (11/5) n^(1/5) (2/(15P) + 2/P^2 + (2 sqrt n/15 + 1)/n) | HAND-DERIVED from (6.2) shape | none | LEAN-KERNEL, CONDITIONAL: Section62b.large_primes in Stage62b.lean, run #19, standard axioms only. Hypotheses carried, NOT proved: hr2 (r2 <= 4M), hR (12 n <= R), hM (M <= (11/5) n^(1/5)); combines lemma42, prime_tail (5.3), prime_count_bound (5.2) |
| Prop 6.1 core (stage 3b) | n = 2m >= 64^4 implies (1/(24 sig m)) sum_{p in PT n} b_p < 2/3, P = floor(2 n^(1/4)) | HAND-DERIVED: u = n^(1/20), final arithmetic value 0.6458 < 2/3 | none | LEAN-KERNEL, CONDITIONAL: Section63b.prop61_core in Stage63b.lean (merged file) and Section63.numeric_core / final_arith in Stage63a.lean, GitHub run #23 (0e26978), axioms [propext, Classical.choice, Quot.sound] only, no sorryAx. Hypotheses carried, NOT proved: h31 (Prop 3.1 for p <= Pn, i.e. Lemma 3.2 open) and hr2 (two-square count r2 <= 4 Mn). Mn is not yet linked to Section42.R2 beyond hr2, and R = 24 sig m is stated, not derived from Jacobi |
| Conditional assembly (Section64) | odd m, all prime factors 3 mod 4, 64^4 <= 2m, plus hr2, h31, hJ (16 sig m <= abs Rmix(2m)) imply exist Good a, Good b with a + b = 2m | HAND-DERIVED: prop61_core times 24 sig m gives sum b_p < 16 sig m; then Sufficiency.sufficiency | none | LEAN-KERNEL, CONDITIONAL: Section64.euler_conditional and Section64.hJ_of_jacobi in Stage64.lean (merged: Stage63b + Sufficiency23 + FourSquaresMixed + Section64), GitHub run #25 (72f57c6), axioms [propext, Classical.choice, Quot.sound] only. Section42.Rmix = Sufficiency.Rmix and Section42.bp = Sufficiency.bp both closed by rfl. Hypotheses carried, NOT proved: h31 (Lemma 3.2 open), hr2 (two-square count), Jacobi |R(n)| = 24 sig m (hjac in hJ_of_jacobi). This is NOT Euler's conjecture |
| Two-square count, reductions (Stage66a) | |S u| <= |S(u/p^2)| for p = 3 mod 4 prime dividing u; |S u| <= |S(u/2)| for 2 | u; |S 1| = 4, where S u = integer pairs with a^2+b^2 = u | HAND-DERIVED | none | LEAN-KERNEL: TwoSq.inert_le, two_le, S1_card, GitHub run #31 (51a2684), standard axioms only. S is `noncomputable` (Finset.Icc on Z). Not hr2: no primes q = 1 mod 4, no Mq, R2, Mn |
| Two-square count, splitting (Stage66b) | |S(q t)| + |A inter B| = 2 |S t| for prime q and x^2+y^2 = q, A and B the images of S t under multiplication by x+yi and x-yi | HAND-DERIVED | none | LEAN-KERNEL: TwoSq.split_sum, run #31 (51a2684), standard axioms only. Counts nothing about A inter B yet (stage 66c) |
| Two-square overlap and closed form (Stage66c) | for prime q = 1 mod 4 with x^2+y^2 = q: q does not divide t gives |S(q t)| = 2 |S t|; |S(q(q s))| + |S s| = 2 |S(q s)|; q does not divide v gives |S(q^e v)| = (e+1) |S v| | HAND-DERIVED | none | LEAN-KERNEL: TwoSq.split_nodvd, split_dvd, closed_form, GitHub run #34 (4c2250c), standard axioms only. Does not mention Mq, R2 or Mn |
| Final conditional theorem (Section65) | for every n = 2 mod 4: exist Good a, Good b with a + b = n, given Hr2, H31, HJac (each universal over odd m with all prime factors 3 mod 4 and 64^4 <= 2m, except HJac over odd m) | HAND-DERIVED: analytic_range_of from Section64.euler_conditional + hJ_of_jacobi, then Euler1747.euler_1747_of_analytic_range | none | LEAN, CONDITIONAL: Section65.euler_1747_conditional in Stage65.lean (Stage64 + Euler1747 merged), GitHub run #27 (7955c9c), axioms [propext, Classical.choice, Quot.sound, Euler1747.allOk_true._native.native_decide.ax_1_1]. The native_decide axiom comes from the finite range n < 64^4 (compiler-trusted, not kernel-only) and stays even after Hr2, H31, HJac are discharged. Euler1747 #eval printed 43 and some 313, matching the paper |
| Hurwitz count equals FourSq.R (Stage68a) | for even n, the set of Hurwitz quaternions of norm n has ncard equal to (FourSq.R n).card, where FourSq.R is the integer four-square solution set restated from CatGT-side FourSq; Lipschitz count = R n for all n | HAND-DERIVED | none | LEAN-KERNEL: Section68.lipschitz_eq_R, Section68.hurwitz_ncard_eq_R (with HurwitzA.hurwitz_ncard_eq_lipschitz), fast run #5 (ec731b7), no sorry, no error, axioms [propext, Classical.choice, Quot.sound] only. This is a counting bridge only: it does not prove the Jacobi four-square formula and does not discharge HJac, which still needs Hurwitz Euclidean division and unique factorization |
| p | m case of H31 (Stage69a) | for m odd, p prime, p % 4 = 3, p ∣ m, and the hypothesis hmix (∀ m' odd, (Rmix (2m')).card = 16 σ(m')): bp p (2m)/(24σ(m)) ≤ 2/(p(p−1)) + (if 3 < p then τ(m)√m/(3σ(m)) else 0). Proof by coordinate division counting | HAND-DERIVED | none | LEAN-KERNEL: Section69.h31_dvd, bp_card, sig_ge_sq, Eset_eq_image, euler-stage66 run #7 (19a4e3e), no sorry, no error, axioms [propext, Classical.choice, Quot.sound] only for all four. It covers only the p ∣ m branch of H31 and takes hmix as a hypothesis (derivable from HJac + FourSq.mixed_count, not yet done here). It does NOT cover p ∤ m (p = 3 and p > 3), which stays inside H31 |
| Euler 1747 for n = 2 mod 4 conditional on H31ndvd and HJac only (Stage70) | H31ndvd is H31 restricted to primes p = 3 mod 4 NOT dividing m (same bound, same side conditions). Theorem: H31ndvd and HJac imply Euler's conjecture for n = 2 mod 4. Route: hmix_of_hjac (HJac and FourSq.mixed_count give |Rmix(2m)| = 16 sigma(m) exactly), then Section69.h31_dvd handles p dividing m, so H31ndvd plus HJac gives H31, then Section65.euler_1747_of_H31_HJac | HAND-DERIVED | none | LEAN-KERNEL: Section70.hmix_of_hjac, h31_of_ndvd, euler_1747_of_H31ndvd_HJac and Section69.h31_dvd, integration run #3 (commit 4302767, 23m), no sorry, no error. Axioms: hmix_of_hjac, h31_of_ndvd, h31_dvd [propext, Classical.choice, Quot.sound]; the final theorem [propext, Classical.choice, Quot.sound, Euler1747.allOk_true._native.native_decide.ax_1_1] (native_decide on the finite range n < 64^4, as before). Remaining hypotheses are exactly H31ndvd (p = 3 and p > 3 with p not dividing m) and HJac (needs Hurwitz Euclidean division and unique factorization). Linter warnings in the older Stage67 code (unreachable tactic) are unchanged and are not errors |
| Hurwitz covering lemma (Stage71a) | for every x in Q^4 there is q with all coordinates integers or all in Z + 1/2 and sum (x_i - q_i)^2 < 1. Proof: round each coordinate (error at most 1/2, square at most 1/4); if some error is below 1/2 the sum is below 1, otherwise every x_i is in Z + 1/2 and q = x | HAND-DERIVED | none | LEAN-KERNEL: Section71.cover, euler-stage66 run #9 (commit 143a765), no sorry, no error, axioms [propext, Classical.choice, Quot.sound] only; one deprecation warning for push_neg, harmless. This is the rounding step only: it does not define the Hurwitz order as a ring, prove it closed under multiplication, or prove Euclidean division, and does not discharge HJac |
| Hurwitz division with remainder, approximate form (Stage71b) | for rational quaternions a, b with b != 0 there is q (Hurwitz coordinates) with N(a - q b) < N(b). Proof: apply the covering lemma to a b^-1, then a - q b = (a b^-1 - q) b and N is multiplicative. NOT closure of the Hurwitz order under multiplication, NOT unique factorization, NOT HJac | HAND-DERIVED | none | LEAN-KERNEL: Section71b.hur_div_approx, euler-stage66 run #12 (commit e83f666), axioms [propext, Classical.choice, Quot.sound], no sorry |
| Hurwitz lattice closed under multiplication, addition, negation (Stage71c) | for rational quadruples that are all integers or all in Z + 1/2, the Hamilton-product formulas (ae-bf-cg-dh, af+be+ch-dg, ag-bh+ce+df, ah+bg-cf+de) again give such a quadruple; also sums, negatives, and 1. Proof: split on parity of S = p+q+r+s (mixed case) or T = p+..+t (half x half); all four components land in the same class. NOT proved here: that these formulas are Mathlib's Quaternion Q multiplication (done in Stage71d), a bundled Subring, unique factorization, HJac | HAND-DERIVED | none | LEAN-KERNEL: Section71c.H_mul, H_add, euler-stage66 run #13 (commit 29fe827), axioms [propext, Classical.choice, Quot.sound], no sorry |
| Euclidean division in the Hurwitz order, left-quotient form (Stage71d) | for rational quaternions a, b whose coordinates are Hurwitz quadruples, b not zero: there is q with Hurwitz coordinates such that a - q b has Hurwitz coordinates and N(a - q b) < N(b). Proof: Stage71b gives q with N(a - q b) < N(b); q b is Hurwitz by Stage71c identified with Mathlib's product via the four component identities; a - q b = a + (-(q b)) is Hurwitz by H_add, H_neg. NOT proved: a bundled Subring or EuclideanDomain instance (the order is non-commutative), unique factorization of primitive elements, Jacobi's count, HJac. Note: some fallback alternatives in the component-identity proofs are unused (linter warnings only) | HAND-DERIVED | none | LEAN-KERNEL: Section71d.hurwitz_euclid, euler-stage66 run #15 (commit 93274f7), axioms [propext, Classical.choice, Quot.sound], no sorry |
| Step A: no half-integer Hurwitz numerators of even norm (HurwitzStepA) | for even n, the set of numerators u (entries all even or all odd, sum of squares 4n) has the same ncard as the set of integer 4-tuples of sum of squares n. Proof: four odd squares sum to 4 mod 8 but 4n = 0 mod 8 for even n, so every such u is all-even, u = 2x. This is a statement about integer numerator tuples, NOT about the Hurwitz ring, and NOT r4(2m) = 24 sigma(m) | HAND-DERIVED | none | LEAN-KERNEL: HurwitzA.hurwitz_ncard_eq_lipschitz, euler-stage66 run #17 (commit 8c36808), axioms [propext, Classical.choice, Quot.sound], no sorry |
| Exactly 24 Hurwitz quadruples of norm 1 (Stage72a) | the set of rational quadruples that are all integers or all in Z + 1/2 with sum of squares 1 has ncard 24. Proof: numerators u = 2x are bounded by 2, the finite set of numerators is counted by decide +kernel, and the count is transported through the injective map u -> u/2. NOT proved: that these 24 are the units of the Hurwitz order (inverse = conjugate), nor any count for other norms. The 8 + 16 split was hand-derived, not separately formalized | HAND-DERIVED | none | LEAN-KERNEL: Section72a.units_count, euler-stage66 run #17 (commit 8c36808), axioms [propext, Classical.choice, Quot.sound], no sorry; U is marked noncomputable (decidability instance), linter warnings about unused fallback tactics only |
| Right-sided Euclidean division in the Hurwitz order (Stage73a) | for rational quaternions a, b whose coordinates are Hurwitz quadruples, b not zero: there is q with Hurwitz coordinates such that a - b q has Hurwitz coordinates and N(a - b q) < N(b). Proof: apply Stage71d (hurwitz_euclid) to the conjugates star a, star b; star is an anti-automorphism (star_mul, star_sub, star_star) that preserves the norm and Hurwitz coordinates (QH_star, normSq_star'). NOT proved: the divisor lemma (hand-derived in the project note, not in Lean), principal right ideals as a bundled statement, the count 24(p+1), HJac | HAND-DERIVED | none | LEAN-KERNEL: Section73a.hurwitz_euclid_right, euler-stage66 run #19 (commit f54689e), axioms [propext, Classical.choice, Quot.sound], no sorry; linter warnings about unused fallback tactics only |
| Hurwitz algebra basics (Stage73b) | components of the quaternion product and star; 1 is Hurwitz; a Hurwitz element of norm 1 has a Hurwitz two-sided inverse (its conjugate) | LEAN-KERNEL, run #22, standard axioms | Stage73b.lean (unit_inv, QH_one, four_normSq_nat) | feeds Stage73d/e |
| Hurwitz norm is a natural number (Stage73c) | for QH x, normSq x is a natural number (integer coordinates: sum of squares; half-integer: sum of p^2+p plus 1) | LEAN-KERNEL, run #25, standard axioms | Stage73c.lean (normSq_nat) | feeds min_gen |
| Right ideals of H are principal; generators (Stage73d) | a nonzero right ideal (predicate: Hurwitz, closed under subtraction and right multiplication by Hurwitz) is gH for a minimum-norm g (uses hurwitz_euclid_right); two generators of one ideal differ by a right unit; g*u generates the same ideal for a unit u | LEAN-KERNEL, run #25, standard axioms | Stage73d.lean (min_gen, gens_unit, unit_gen_mem) | feeds Stage73e |
| 24 units and 24 generators (Stage73e) | {u : Quaternion Q | QH u and normSq u = 1} has 24 elements (Stage72a count transported); every principal right ideal gH, g != 0, has exactly 24 generators | LEAN-KERNEL, run #27, standard axioms | Stage73e.lean (units_QH_count, gens_count) | next: reduction mod p, p+1 right ideals of norm p, recurrence h(n)=(p+1)h(n/p)-p h(n/p^2) (see DERIVATION-hjac doc) |
| Final theorem with Hr2 discharged (Stage67) | for every n = 2 mod 4: exist Good a, Good b with a + b = n, given only H31 and HJac | HAND-DERIVED: euler_1747_conditional applied to Section65.hr2 | none | LEAN, CONDITIONAL: Section65.euler_1747_of_H31_HJac (h31 : H31) (hjac : HJac), integration run #1 (747ddd5) green, no sorry, no error. Axiom list, read in full from integration run #2 (ec731b7, run 44148034557, which printed the continuation lines): [propext, Classical.choice, Quot.sound, Euler1747.allOk_true._native.native_decide.ax_1_1]. The native_decide axiom comes from the finite range n < 64^4 (compiler-trusted, not kernel-only), the same as for Section65.euler_1747_conditional; it stays after H31 and HJac are discharged. The remaining hypotheses are exactly H31 and HJac |
| Prop 3.1 | b_p/R <= 2/(p(p-1)) + [p>3] tau sqrt m / (3 sigma) | COMPUTED: 3,059 (m,p) cases, 0 violations, one equality case (m=7, p=3) | audit_prop31.py | LEAN: needs Hurwitz order + finite quotient + Lemma 3.2. Not feasible near-term |
| Lemma 3.2 | \|\|T_m\|\| <= tau(m) sqrt m on {1,chi}^perp | COMPUTED: 82 instances (22 + 60), 0 violations. m=1 is an EQUALITY (ratio exactly 1, trivial: T_1 = identity) and is listed separately, not counted in the worst ratio. Worst NONTRIVIAL ratios: 0.8752 (p=7, m=47), 0.9156 (p=11, m=31), 0.9764 (p=19, m=59), 0.9517 (p=23, m=53), 0.9820 (p=31, m=5; largest nontrivial ratio seen), all from a separate sweep of odd m <= 61 with p not dividing m, 0 violations (these sweeps overlap the 82 listed above in part; distinct-instance count not established); earlier p=3 partial run | audit_lemma32.py | General Lean proof OPEN: the full spectral bound needs Jacquet-Langlands and weight-two Ramanujan-Petersson (Deligne), neither in Mathlib. The two exceptional modes (T_m 1 = sigma(m) 1, T_m chi = (m/p) sigma(m) chi) are a finite-group statement that could be formalized separately. Hecke identification (3.5) and "exactly {1,chi}" are READ only. Another assistant reports seven exact checks at p=7; not reproduced or merged with our 22 |
| Lemma 4.1 | Nmix(t) <= 2(t+1) | LEAN-KERNEL (integer t): Section4.Nmix_le in Lemma41.lean, standard axioms only, GitHub elementary run #2 green; also COMPUTED for t in [0,4000] | Lemma41.lean, audit_lemma4.py | real-t reduction to floor not formalized |
| Lemma 4.2 | (1/R) sum_{p>P} b_p <= (4/3) M(n) [ ... ] | COMPUTED: 1,164 tests, 0 violations, worst lhs/rhs 0.442 | audit_lemma4.py | LEAN-KERNEL, CONDITIONAL: Lemma42.lean (Section42.bp_le_16: bp <= 16 M (n/(p*p)+1); bp_zero: bp = 0 when n < p*p; lemma42: the summed (4.1) over p with p*p <= n), standard axioms only, GitHub elementary run #12 (commit 19411d9). Axiom list does NOT show the hypotheses it takes: hr2 (two-square count r2(u) <= 4M for 1 <= u <= n in the box, not in Mathlib, not proved) and hR (R >= 12n, i.e. Jacobi, not proved) |
| Lemma 5.1 | tau m / sigma <= (23/10) m^(1/5); M(n) <= (11/5) n^(1/5) | COMPUTED: C1^5, C2^5 exact match with the paper's fractions | audit_numbers.py | FIRST BOUND LEAN-KERNEL: Section51.lemma51_first in Lemma51.lean: tau(m) m / sigma(m) <= (23/10) m^(1/5) for m > 0 with every prime divisor = 3 mod 4 (the Lemma 2.1 situation), tau and sigma = Mathlib's sigma 0 and sigma 1; standard axioms only, GitHub elementary run #14 (commit 90efc43). Proved via the multiplicative function F(m) = tau^5 m^4 / sigma^5 <= 183143120027364343/2849934139195392 (= C1^5; Section51.tau_sigma_pow5) and a real fifth root. SECOND BOUND LEAN-KERNEL (GitHub elementary run #19, commit 285cc36, standard axioms only): Section62.Mn_le in Stage62a.lean: Mn n := sup over 1<=u<=n of Mq u (Mq u = product of (e+1) over primes q = 1 mod 4 with q^e || u), Mn n <= (11/5) n^(1/5), via Mq_pow5 (Mq u^5 * 160225 <= 7962624 u). It does NOT prove r2(u) <= 4 Mq(u) (two-square formula, not in Mathlib), so Mn is not yet linked to Section42.R2. LocalFactors.lean (maximisation, run #5, #9) is used by the first bound |
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


## Hypothesis discharge table (Section65.euler_1747_conditional)

Which checked declaration discharges each hypothesis. Updated 2026-11-17. A row says DISCHARGED only when a declaration exists, compiled in a named run, whose statement (read, not just its axiom list) is the hypothesis for every m required.

| Hypothesis | Meaning | Discharged by | Status |
|---|---|---|---|
| Hr2 | card (R2 (2m) u) <= 4 * Mn (2m) for 1 <= u <= 2m | Section65.hr2 (Section66e.hr2_all) | PROVED. Stages 66a-66e, kernel-checked in the euler-stage66 chain (Stage81 run #42 and dev run #5 include it). Superseded earlier status text: pieces in runs #31/#34, Stage66d untested. |
| H31 | Prop 3.1 for p <= Pn (2m) | Section83.h31ndvd_of | PARTLY PROVED. p = 3 (p not dividing m): Section83.bp3 and Section82b.bound3, b_3(2m) <= 8 sigma(m), kernel-checked in Stage83 (dev run #5), standard axioms only. Section83.euler_1747_of_H31gt3 reduces Euler 1747 (n = 2 mod 4) to H31gt3 alone (p > 3, p not dividing m); axioms: standard plus native_decide for the finite range. REMAINING OPEN: H31gt3. Needs Lemma 3.2: Jacquet-Langlands and weight-2 Ramanujan-Petersson, not in Mathlib. Earlier note:  Needs Lemma 3.2: Jacquet-Langlands and weight-2 Ramanujan-Petersson, not in Mathlib. Bridge.pointwise_of_quadform (run #17) only takes the quadratic-form bound hquad as a hypothesis |
| HJac | card (FourSq.R (2m)) = 24 * sig m for odd m | Section80.hjac | PROVED in Lean, run #41 (Stage80a); plugged into Stage70 as Section81.hjac, run #42: propext, Classical.choice, Quot.sound only. Route: Hurwitz order, right ideals Ik (Stage75b/76), key uniqueness/existence (76a/76b), finiteness of Hn (77a), per-key count ncard_Ik_Hn, count_pairs, recur (78a), sg_hecke and h_eq (79a), numerators<->quaternions and norm doubling (80a). Integration with Stage70 done in Stage81 (run #42) |
| 74a-74c | Hurwitz order setup, reduction mod p (red, psi, det_red, red_ker) | Section74b etc. | Kernel-checked in earlier green runs (standard axioms); ledger detail not itemized here |
| 75a, 75b | Hn finite sets, norm doubling (Section75a.double_card); Ik, Ik_ideal, Ik_not_pH, gen_exists | see names | Kernel-checked, run #34 and earlier (standard axioms) |
| 76a, 76b | key_unique, key_exists; Ik_unique, Ik_existsUnique | Section76a/76b | Kernel-checked, runs #35 and #37 |
| 77a | bnd, repr, Hn_finite | Section77a | Kernel-checked, run #37 |
| 78a | ncard_Ik_Hn, count_pairs, zero_count, recur: (p+1)h(m) = h(pm) + [p|m] p h(m/p) | Section78a/b/c | Kernel-checked, run #41 |
| 79a | sg_hecke, h_one, h_eq: h(m) = 24 sg m for odd m | Section79a/b | Kernel-checked, run #41 |
| 80a | num_card, hjac | Section80 | Kernel-checked, run #41; axioms propext, Classical.choice, Quot.sound |
| 81 | Section81.hjac : Section65.HJac; euler_1747_of_H31ndvd | Stage81 | Kernel-checked, run #42 (24m33s, no sorry). Section81.hjac: propext, Classical.choice, Quot.sound. euler_1747_of_H31ndvd: those plus Euler1747.allOk_true._native.native_decide.ax_1_1 (finite range). H31ndvd remains the open hypothesis |

Trust note: even with all three discharged, the finite range (Euler1747.euler_finite) rests on native_decide, so the final theorem would still list the native_decide axiom unless the 4,194,304-case check is redone by a kernel-checked method.

| 82a, 82b | mod-3 fibres: unit_inj, unit_surj, fib_eq; bound3 | Section82a, Section82b | Kernel-checked, dev runs #2 and #3, standard axioms only |
| 83 | bp3, h31ndvd_of, euler_1747_of_H31gt3 | Section83 | Kernel-checked, dev run #5 (Stage83). H31gt3 is the one open hypothesis |


Status 2026-11-18: HJac proved (Section80.hjac, run #41; Section81.hjac, run #42). Hr2 proved (Section65.hr2). H31 reduced to H31gt3 (Section83.euler_1747_of_H31gt3, dev run #5): the only mathematical hypothesis left is Prop 3.1 for primes p > 3 with p not dividing m. Routes to it: Lemma 3.2 (Jacquet-Langlands + Ramanujan-Petersson, not in Mathlib); the one-vector bound <h_p, T_m h_p> <= B(m)||h_p||^2 suffices for the existing bridge; a direct count of bad representations is another possible route; none proved. The reduction does not show every route needs the full operator-norm theorem.
Trust note (still applies to every final theorem): the finite range n < 64^4 uses native_decide, axiom Euler1747.allOk_true._native.native_decide.ax_1_1, not only kernel checking.
| Hybrid budget (conditional, not Lean) | for 1/2 <= beta < 3/5, C = 1, cutoff P(n) = floor(2 n^((1-beta)/2)): the aggregate inequality of Sufficiency.sufficiency follows from hypothesis (H) for all n >= n0 | euler/hybrid-budget/certify_budget.py (exact Fractions, rerun identical) | CONDITIONAL. n0 = 64^4 at beta = 1/2 (that is H31gt3); 10^11 at beta = 0.55 (extra interval (64^4, 10^11]: 24,995,805,696 integers = 2 mod 4 before the factor reduction, uncertified). (H) is NOT proved for any beta < 1. No Lean for the moving-cutoff assembly. |


## Hecke chain on Y_p (layer A, StageA4a to StageA4k)

Added 2026-11-20. Every row: Lean-kernel checked by the "Euler layer A (latest stage)" workflow (compile, no ": error", no sorry, axiom report present, axioms limited to propext, Classical.choice, Quot.sound), conclusion success on the commit named. None of these rows is Prop 3.1 or H31gt3. The operators are on functions on Y_p = PGL2(F_p) / Gamma_p (Gamma_p of order 12, the image of the Hurwitz units); U_n is the sum over Hurwitz quaternions of norm n, T_n = U_n / 24.

| Stage | Statement | Declaration | Commit | Status |
|---|---|---|---|---|
| A4b | T_m self-adjoint for the counting inner product | SectionA4b.Tm_adjoint | b6704ff | Kernel-checked |
| A4c | weighted Hecke counting identity on Hn | SectionA4c.hecke_count | 80a3483 | Kernel-checked, CI green |
| A4d | the same sum over the full norm-l family equals 24 times the right side | SectionA4d.hecke_U | 3693f32 | Kernel-checked, CI green |
| A4e | U_m U_l = 24 (U_lm + l U_m/l), l prime, p not dividing l or m | SectionA4e.hecke_Yp | 53c178c | Kernel-checked, CI green |
| A4f | U_l and U_m commute, l prime | SectionA4f.U_comm | 38b8191 | Kernel-checked, CI green |
| A4g | T_m T_l = T_lm + l T_m/l; T_m T_l = T_l T_m | SectionA4g.Tn_rel, Tn_comm | e22e0fb | Kernel-checked, CI green |
| A4h | U_1 = 24 id, T_1 = id; T_m T_n = T_n T_m for odd n | SectionA4h.U_one, Tn_one, comm_all | 80c88e6 | Kernel-checked, CI green |
| A4i | T_mn = T_m T_n for gcd(m, n) = 1, n odd | SectionA4i.mult | 2044ae4 | Kernel-checked, CI green |
| A4j | T_m 1 = sigma(m) 1, odd m prime to p (input: Section79b.h_eq, copied from Stage80a) | SectionA4j.Tn_const | 827a770 | Kernel-checked, CI green |
| A4k | T_m chi = (m/p) sigma(m) chi, chi the quadratic character of det on Y_p | SectionA4k.Tn_chi | 09638fd | Kernel-checked, CI green (run 44646584114) |

Hand derivations behind these rows are in A4C_PLAN.md (including its Correction section: one generator per key is not right-stable, so the full norm-l family and the factor 24 are needed).

What this chain does NOT establish. (1) Lemma 3.2, the bound ||T_m|| <= tau(m) sqrt m on the orthogonal complement of span{1, chi}: it needs Jacquet-Langlands and the weight-2 Ramanujan-Petersson bound, neither in Mathlib. The two eigenvalue rows (A4j, A4k) are the two exceptional modes only. (2) Prop 3.1 and H31gt3, which remain the one open hypothesis of Section83.euler_1747_of_H31gt3. (3) Even n for the relations that need a Hecke prime (those use 2 invertible mod l). (4) That chi is nonzero or distinct from the constant function. The finite range n < 64^4 still rests on native_decide, as stated above.


## Layer ED: H31gt3 from HPrime (ED/ folder)

Added 2026-11-21. Files ED/EDa1, EDa3 to EDa9, EDb1 to EDb9 compiled one by one against StageA4o and Stage83cut (Stage83 with the namespaces it shares with StageA4o dropped); each returned code 0 with no sorry. Axiom report on the final theorem: propext, Classical.choice, Quot.sound and Euler1747.allOk_true._native.native_decide.ax_1_1. ED/EDa2.lean is unused scratch containing a sorry and is not imported. Compiled in the cloud workspace; not yet run by CI.

| Stage | Statement | Declaration | Status |
|---|---|---|---|
| EDa1 | |PGL2(F_p)| = p(p^2-1) | EDa1.card_PGL2_eq | Compiled, standard axioms |
| EDa9 | 2 |O_p| <= p+1 | EDa9.card_OK_Kp_le | Compiled, standard axioms |
| EDb6 | alpha = x(1+i)^-1 is injective into Q_m | EDb6.alpha_inj, alpha_mem | Compiled, standard axioms |
| EDb7 | b_p(2m) <= #{alpha in Q_m : rho(alpha) in K_p} | EDb7.bp_le_S | Compiled, standard axioms |
| EDb8 | HPrime (Lemma 3.2 for primes, p = 3 mod 4, p > 3) implies Section83.H31gt3 | EDb8.H31gt3_of_hprime | Compiled; conditional on HPrime |
| EDb9 | HPrime implies Euler's conjecture for n = 2 mod 4 | EDb9.euler_1747_of_hprime | Compiled; conditional on HPrime plus native_decide for n < 64^4 |

What this does NOT establish. HPrime itself (Lemma 3.2 for primes) is unproved and not in Mathlib; it needs the Brandt/Eichler identification with S_2(Gamma_0(p)), Eichler-Shimura and the Weil bound. If HPrime were false for an admissible (p, l) the theorem is vacuous. The hypothesis is restricted to p = 3 mod 4, p > 3, which is exactly the range H31gt3 itself quantifies over (p = 3 mod 4, p not dividing m), so nothing further is lost in the reduction. The finite range still rests on native_decide.


## Layer EDc: the Chebyshev (2.04) route, and what is and is not proved about HPrime204Restricted

Added 2026-11-24. Each module compiled in CI on pinned Lean 4.32.0 and Mathlib (rev 81a5d257); the gate fails on any `: error`, any `sorry` in the EDc modules, or any axiom outside {propext, Classical.choice, Quot.sound} in the gated theorems.

| Stage | Compiled statement | Declaration | Tested commit / run | Status |
|---|---|---|---|---|
| EDc2 | `EDb8.HPrime -> EDcDefs.HPrime204Restricted` (bound 2 sqrt(l) implies the relaxed (51/25) sqrt(l), primes l = 3 mod 4) | `EDc2.hprime204_of_hprime` | d35244f, Actions run 45498404409 (Euler EDc2), 21m 12s | Compiled; axioms [propext, Classical.choice, Quot.sound]. An IMPLICATION: it assumes HPrime. |
| EDc2 | `EDcDefs.HPrime204Restricted -> EDcDefs.H31gt3A` (the A-shaped H31gt3, tau(m) replaced by Amaj (51/50) m) | `EDc2.H31gt3A_of_hprime204` | d35244f, run 45498404409 | Compiled; axioms [propext, Classical.choice, Quot.sound]. An IMPLICATION: it assumes HPrime204Restricted. |
| EDc3 | for every admissible n and every f in L^2(Y_p): `||Tl n f|| <= sigma(n) * ||f||`, no hypothesis | `EDc3.Tl_norm_le` | 2609aaf, Actions run 45505211132 (Euler EDc3), 2m 21s | Compiled; axioms [propext, Classical.choice, Quot.sound]. UNCONDITIONAL. |
| EDc3 | for a prime l with Adm p l and every f: `||Tl l f|| <= (l + 1) * ||f||` | `EDc3.Tl_prime_norm_le` | 2609aaf, run 45505211132 | Compiled; axioms [propext, Classical.choice, Quot.sound]. UNCONDITIONAL. |
| EDc3 | helpers: `sq_norm_sum_le` (Cauchy-Schwarz for a finite complex sum), `U_sq_le` and `Tn_sq_le` (pointwise Cauchy-Schwarz for U_n and T_n = U_n / 24), `sg_prime` (sigma(l) = l + 1) | `EDc3.*` | 2609aaf | Compiled; each is a dependency of the two theorems above, so its axioms are contained in theirs. |

Proof of EDc3 (Schur test), on declarations already checked in StageA4o: `U_mk` writes U_n f at a coset as a sum over the 24 sigma(n) Hurwitz elements of norm n; Cauchy-Schwarz gives |T_n f(y)|^2 <= sigma(n) T_n(|f|^2)(y); summing over Y_p with `Tl_symm` (self-adjoint) and `T_n 1 = sigma(n) 1` (`Tn_const`) gives ||T_n f||^2 <= sigma(n)^2 ||f||^2.

What is proved about HPrime204Restricted. Nothing about its conclusion. HPrime204Restricted says: for every prime p = 3 mod 4 with p > 3, every prime l = 3 mod 4 with Adm p l, and every f orthogonal to span{1, chi} in L^2(Y_p): ||T_l f|| <= (51/25) sqrt(l) ||f||. EDc3 proves only ||T_l f|| <= (l + 1) ||f||, which holds for ALL f and is strictly weaker: (l + 1) > (51/25) sqrt(l) for every prime l >= 3 (at l = 3, 4 against about 3.53). It therefore discharges HPrime204Restricted for no (p, l). EDc2 is implications only. Self-adjointness, the eigenvalues on 1 and chi, multiplicativity and the prime-power recursion (`Tl_symm`, `Tl_one_eig`, `Tl_chi_eig`, `Tl_mul`, `Tl_rec`, StageA4o) are the elementary part and are checked.

What is still ASSUMED, exactly. The size of the eigenvalues of T_l on the orthogonal complement of span{1, chi}. By Jacquet-Langlands these are Hecke eigenvalues a_l of weight-2 cusp forms with trivial character and level dividing 2 p^2, and the missing input is |a_l| <= 2 sqrt(l) for primes l not dividing 2p (Eichler-Shimura plus Weil/Deligne). Mathlib has neither Jacquet-Langlands nor Ramanujan-Petersson. HPrime204Restricted is OPEN; the remaining gap is the factor from (l + 1) down to (51/25) sqrt(l).

Housekeeping. The CI summary prints the EDc3 and EDc2 last axiom line twice (the gate's `grep -A2` captures the next report); cosmetic. EDc2.lean.bak is untracked in the working copy and has not been compared with the tracked file.


## Layer EDc, continued: EDc4, EDc4b, EDc5 (the eigenvalue-level hypothesis RPEigen)

Added 2026-11-25. Same CI gate as above. RPEigen is OPEN and not proved in this development; every theorem below is an implication from it.

| Stage | Compiled statement | Declaration | Tested commit / run | Status |
|---|---|---|---|---|
| EDc4 | spectral reduction: for a symmetric T on a finite-dimensional complex inner product space with every real eigenvalue bounded by B (B >= 0), `||T f|| <= B ||f||` | `EDc4.norm_le_of_eigen_bound` | acb5161, Actions run 45516998200 (Euler EDc4), 14m 41s | Compiled; axioms [propext, Classical.choice, Quot.sound]. UNCONDITIONAL linear algebra. |
| EDc4 | `EDc4.RPEigen -> EDcDefs.HPrime204Restricted` | `EDc4.hprime204_of_rpeigen` | acb5161, run 45516998200 | Compiled; axioms [propext, Classical.choice, Quot.sound]. An IMPLICATION: it assumes RPEigen. |
| EDc4b | the same spectral lemma, plus `norm_le_on_invariant` (the bound on an invariant submodule) | `EDc4b.norm_le_of_eigen_bound`, `EDc4b.norm_le_on_invariant` | 641250d, run 45517469683 (Euler EDc4b) | Compiled; axioms [propext, Classical.choice, Quot.sound]. UNCONDITIONAL. |
| EDc4b | `EDc4b.RPEigen -> EDcDefs.HPrime204Restricted`; a second elaboration route with its own copy of RPEigen (same statement as EDc4.RPEigen) | `EDc4b.hprime204_of_rpeigen` | 641250d, run 45517469683 | Compiled; axioms [propext, Classical.choice, Quot.sound]. An IMPLICATION. Cross-check of EDc4, not a stronger result. |
| EDc5 | `EDc4.RPEigen -> EDcDefs.H31gt3A`, composition of `EDc4.hprime204_of_rpeigen` and `EDc2.H31gt3A_of_hprime204` | `EDc5.H31gt3A_of_rpeigen` | 641250d, run 45517469709 (Euler EDc5), importing EDc4 as of 641250d | Compiled; axioms [propext, Classical.choice, Quot.sound]. An IMPLICATION. No new mathematics. |

RPEigen (EDc4), exactly. For every p (Fact prime) with p = 3 mod 4, p > 3, h2, xs, ys, hxy as in HPrime204Restricted, every prime l = 3 mod 4 with Adm p l, every real mu and every nonzero f in L^2(Y_p) with <1, f> = 0, <chi, f> = 0 and T_l f = mu f: |mu| <= 2 sqrt(l). The binders match HPrime204Restricted line for line.

Earlier failures, classified separately (elaboration errors, not mathematical failures).
- Euler EDc4 on ff2ff49 (run 45508964617): type mismatch at EDc4.lean:122:66, a hand-written type for the restricted symmetry fact. Fixed in 4e322fc.
- Euler EDc4 on 4e322fc (run 45513047458): EDc4.lean:135, the subspace type of the spectral lemma call could not be determined. Fixed in acb5161.
- Euler EDc5 on 9c17cf0 (run 45515356276): DEPENDENCY failure, the same EDc4.lean:135 error compiled inside its chain. It never reached EDc5's own theorem and does not validate or refute it. EDc5's validating run is 45517469709 on 641250d.

What is still assumed, exactly. RPEigen. Its content: (1) the Jacquet-Langlands identification of the eigenvalues of T_l on {1, chi}^perp with Hecke eigenvalues a_l of weight-2 cusp forms (trivial character, level dividing 2 p^2, Hecke normalisation T_l 1 = (l + 1)); (2) the bound |a_l| <= 2 sqrt(l) (Eichler-Shimura plus Weil/Deligne); (3) the component count excluding exceptional constituents beyond span{1, chi}. Mathlib has none of these. These identifications are claims requiring source verification; the compiled results above do not verify them. The constant 2 lives entirely inside RPEigen: EDc4 proves the passage from eigenvalue bounds to operator bounds, nothing about their size.


## Layer EDc, continued: EDc6 (finite bookkeeping toward the Codogni-Lido kernel description)

Added 2026-11-25. Tested on 1779f19, Actions run 45529719670 (Euler EDc6), 3m 1s. This is elementary finite bookkeeping; it does not touch RPEigen.

| Stage | Compiled statement | Declaration | Status |
|---|---|---|---|
| EDc6 | chi takes only the values 1 and -1 on Y_p | `EDc6.chiY_eq_one_or_neg_one` | Compiled; axioms [propext, Classical.choice, Quot.sound]. UNCONDITIONAL. |
| EDc6 | `<1, f> = sum_y f y` | `EDc6.inner_oneY` | Compiled; same axioms. UNCONDITIONAL. |
| EDc6 | `<chi, f> = sum_y chi(y) f(y)` | `EDc6.inner_chiE` | Compiled; same axioms. UNCONDITIONAL. |
| EDc6 | `(<1,f> = 0 and <chi,f> = 0)` iff (sum of f over {chi = 1} is 0 and sum of f over {chi = -1} is 0) | `EDc6.orth_iff_fibre_sums` | Compiled; same axioms. UNCONDITIONAL. |

What this does NOT establish. It does not identify the level sets {chi = +-1} with the Weil-invariant fibres of Codogni-Lido (J. Number Theory 286 (2026) 131-184, Remark 2.3.6, p. 150-151), does not identify T_l with their adjacency operator, and does not prove or assume their Theorem 2.3.8 = 4.18 (p. 165). Those three bridges (vertices = Y_p; T_l = A or A^t including orientation and 1/24 weights; Weil fibres = chi level sets) are written out in the specialist package `claude/PACKAGE-euler-rpeigen-specialist-review-2026-11-25.md` and are NOT verified. RPEigen stays OPEN.

## Layer EDc, continued: EDc7 (finite bookkeeping: transport of the Hecke setup along a conjugacy of splittings)

Added 2026-11-25. Tested on 8de758f, Actions run 45532991247 (Euler EDc7 (Lean)), 2m 54s, success. Earlier run 45531890387 on f963c26 failed because a stale copy of the file was compiled; superseded.

Kind of result: finite bookkeeping, CONDITIONAL on the hypothesis `EDc7.Conj` (a matrix c in GL_2(F_p) with red' x = c (red x) c^-1 on the relevant quaternions). `Conj` is not proved in EDc7; it is the Skolem-Noether step.

| Declaration | Kind | Axioms |
|---|---|---|
| `EDc7.conjP_conjP_inv`, `EDc7.conjP_injective` | unconditional, conjugation on PGL2 | [propext, Classical.choice, Quot.sound] |
| `EDc7.rhoT_conj`, `EDc7.rho_conj`, `EDc7.Gam_conj`, `EDc7.chiP_conj` | conditional on `Conj` | same |
| `EDc7.transport` | conditional on `Conj`: bijection Y_p to Y_p' preserving chi and intertwining U | same |

Does NOT establish: `Conj` itself, any eigenvalue bound, or any link to elliptic curves. RPEigen stays OPEN and is not proved in this development.

## Layer EDc, continued: EDc8, EDc9, EDc10 (tested on 59af1de) and EDc11 (earlier failed run)

Added 2026-11-25. Tested on 59af1de; Actions runs: EDc8 45534909558 (27m 25s), EDc9 45534909592 (14m 39s), EDc10 45534909526 (25m 57s), all success; every gated declaration passed the declaration-specific parser `euler/lean/agents/check_axioms.py` with axioms exactly [propext, Classical.choice, Quot.sound]. The "Euler ED layer (lake build)" run 45534909436 failed with a 503 while downloading elan (infrastructure, not a proof error).

| Module | Declaration(s) | Kind of result |
|---|---|---|
| EDc8 | `EDcSplitTransport.exists_red_conjugator`, `conj_of_splittings` | NEW PROOF (finite algebra): explicit matrix conjugator between any two splittings; this discharges the hypothesis `EDc7.Conj` for every pair of splittings (no Skolem-Noether invoked). |
| EDc8 | `Lmap_inner`, `Lmap_Tl` | FINITE BOOKKEEPING: composition with the transport bijection preserves the inner product and intertwines Tl. |
| EDc8 | `rpeigenAt_transport`, `rpeigenAt_all`, `rpeigen_of_one_splitting` | CONDITIONAL REDUCTION: RPEigen at one splitting implies it at every splitting; RPEigen is the hypothesis, not proved. |
| EDc9 | `WeilFibre.chiY_rhoT_mul`, `Tl_support_shift`, `Tl_preserves_orth`, `Tl_preserves_fibre_sums_zero` | FINITE BOOKKEEPING: Tl shifts chi-support by (n/p); the subspace orthogonal to 1 and chi (= fibre-sum-zero, EDc6) is Tl-invariant. No eigenvalue estimate. |
| EDc10 | `EulerVertexDraft.mem_ker_rho_iff`, `unitRed_central_iff`, `card_HurU_eq_card_Gam_mul_card_ker`, `card_HurU_twelve_two` | FINITE BOOKKEEPING: ker(Hurwitz units to PGL2) = {1,-1}; 24 = 12*2. |
| EDc10 | `linearLevelVertexEquiv`, `mem_liftedGamma_iff`, `unit_stabilizer_iff` | FINITE BOOKKEEPING: coset equivalence for the lifted subgroup; uniform stabiliser +-1. |

What none of this establishes: RPEigen; any eigenvalue bound; identification of Y_p with supersingular curves (Deuring); identification of the Weil fibres with the chi level sets; applicability of Codogni-Lido. RPEigen stays OPEN and is not proved in this development.

Historical EDc11 status, superseded below. Run 45534909557 on 59af1de FAILED. First compiler error: `EDc11.lean:224:61: error: unsolved goals` in `EdgeCount.Tmat_symm` (goal N_ij/2 = N_ji/2 after `rw [card_end_symm ...]`). The same run's axiom output showed `card_end_symm` and `Tmat_symm` depending on `sorryAx` (a consequence of the failed run; cause of the former not yet understood). `card_cos_eq`, `U_matrix`, `Tn_matrix` were clean. A repair of `Tmat_symm` is committed locally and UNTESTED until it runs on CI; EDc11 is not recorded as established.


## EDc11 verified on current main, 2026-11-25

Source and CI-tested commit `01c4210aed1c422eae8530dc8b8c2e8e48bec378`, direct child of `a7b8bdf`. [Run 45564773560, job 139036797473](https://github.com/TOTOGT/DM3-lab/actions/runs/45564773560/job/139036797473) completed successfully, including the pins and compile-and-gate steps. The gate enforced a subset of `[propext, Classical.choice, Quot.sound]` individually for all five declarations. Raw job logs required authentication, so this entry does not claim the exact printed lists were independently retrieved. The successful gate excludes `sorryAx` in `card_end_symm` and the other four declarations on this commit.

With p prime, 2 nonzero in ZMod p, xs²+ys²=−1, l natural and p∤l, `EdgeCount.card_cos_eq` gives `#NCos(g,h) = 12 * #NEnd(g,h)` and `card_end_symm` equates the two counts on reversing exact endpoints. `Tmat_symm` gives symmetry of the rational matrix on the chosen representatives. With the finite quotient instance, `U_matrix` and `Tn_matrix` prove the actions on every complex function at every vertex, with coefficients `12*Nmat` and `Nmat/2` respectively. No spectral hypothesis occurs. The geometric edge multiplicity and `RPEigen` remain open.

## Integrated local vertex and fibre results, 2026-11-25

`VertexDoubleOrbit` (five gated declarations, tested source `7c57574`) and `FibrePushforward` (six, tested source `1ccdfc8`) were locally compiled with Lean 4.32.0 and Mathlib `81a5d257c8`. All eleven archived reports give exactly `[propext, Classical.choice, Quot.sound]`. Integration on base `01c4210` reproduced each complete dependency key and rechecked the axiom reports. See `euler/lean/agents/lanes/` for full statements, commands and compiler exits. The separate Actions workflow awaits publication and its first run.

The vertex equivalence identifies the Hurwitz-unit/scalar double orbit with `Yp` and counts two stabilizing units per projective point. Fibre transport identifies the two orthogonality conditions with a zero fibre pushforward, given a finite vertex bijection and the matching character labels. Swapping the labels preserves the kernel. Geometric vertex and label identification, operator comparison and the spectral input remain outstanding.
