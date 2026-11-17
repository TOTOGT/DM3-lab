# Audit: Howe-Huffman-Kohlmeyer-Kruer, "Euler's 1747 conjecture", sections 2-6 (hexagon:2611.00370v1)
Date: 2026-11-16. Auditor: Claude (Cowork). Source text read: the user-supplied PDF as extracted to text, sections 2-6 read in full; section 7 and Lean side done separately.
Labels: READ = I read it and followed the step; COMPUTED = reproduced by a script (scripts: audit_numbers.py, audit_prop31.py, in ~/Desktop/EulerLean); NOT CHECKED = not verified by me.

## Section 2 (reduction, Jacobi count, eq 2.1-2.3)
- Lemma 2.1 reduction: READ; also reproduced in Lean (Euler1747.lean, euler_1747_of_analytic_range).
- (2.1) R(n)=24 sigma(m) for n=2m, m odd: READ + COMPUTED (brute force, every tested m).
- (2.2) |Rmix| = (2/3)R: READ + COMPUTED + Lean-kernel-checked (FourSquaresMixed.lean, standard axioms only).
- "-1 nonresidue => p | x^2+y^2 implies p | x,y" and the sufficiency of (2.3): READ, followed.

## Section 3 (Hurwitz order, Hecke operator, Prop 3.1)
- |Gamma_p|=12, |Y_p|=p(p^2-1)/12, |O_p|=(p+1)/2, mu_p=6/(p(p-1)), factor 8, eq (3.6)-(3.8): READ, re-derived line by line, all consistent.
- Prop 3.1 as stated: COMPUTED. Brute force over all odd m<2400 with every prime factor = 3 mod 4 (3059 pairs (m,p)): 0 violations; one case (m=7,p=3) meets the bound with equality (1/3).
- Lemma 3.2 TESTED DIRECTLY (COMPUTED, audit_lemma32.py): built H/pH = M2(F_p), Y_p = Gamma_p \ PGL2(F_p), and T_m of eq (3.4) from the Hurwitz quaternions of norm m. For p = 7, 11, 19 (|Y_p| = 28, 110, 570) and 22 odd m in {3..45}: |Y_p| matched p(p^2-1)/12, |Q_m| matched 24 sigma(m), T_m was symmetric, T_m 1 = sigma(m) 1 and T_m chi = (m/p) sigma(m) chi held to ~1e-14, and the largest |eigenvalue| on {1,chi}^perp was always below tau(m) sqrt(m): 0 violations, worst ratio 0.957 (p=19, m=7: 5.0642 vs 5.2915); ratios grow with p. Earlier partial run also had p=3 (0 violations). An independent report relayed by the user (another assistant, p=7, m in {3,5,9,15,25,27,45}, bound 3.026 for m=5 vs 4.472) is consistent with my exact value 2.8284 for p=7, m=5, but that report itself is UNVERIFIED by me.
  Still READ only: the identification (3.5) and the claim that 1 and chi_p exhaust the one-dimensional automorphic representations; the tests above support the OUTCOME in 22+ instances, they do not prove the general lemma.
- (earlier line) Lemma 3.2: READ only. Rests on Jacquet-Langlands + the Ramanujan-Petersson bound (Deligne) for weight 2. NOT CHECKED independently: the identification (3.5) of the class set with Y_p and the Hecke normalisation. The brute-force test above is empirical support for the OUTCOME, not a proof of the lemma.

## Section 4 (large primes)
- Lemma 4.2's chain (b_p <= 16 M(n)(n/p^2+1), sum over p<=sqrt n, R>=12n): READ, consistent. Lemma 4.1 (Nmix(t) <= 2(t+1)): READ, NOT tested numerically.

## Section 5 (explicit constants)
- C2^5 = 7962624/160225 < (11/5)^5: COMPUTED, exact match.
- C1^5 = 183143120027364343/2849934139195392 < (23/10)^5: COMPUTED, exact match (uses the p/(p+1) form).
- (5.2), (5.3): COMPUTED, no violation in tested ranges. (5.4) partial sum 0.41707 < 0.42: COMPUTED.

## Section 6 (Prop 6.1)
- (6.1) = 140029/259200, (6.2) = 1103927/11059200, sum = 21235493/33177600 = 0.64006 < 2/3: COMPUTED, exact match with the paper.
- Side bounds X^(-1/5) <= 4/9, 2^(3/10) < 5/4: COMPUTED.
- Real-valued bound at X=64 is 0.6337; decreasing in X (X=100,1000,10^4 tested).

## Verdict
No error found in sections 2-6. Every explicit number reproduces. The deep spectral input (Lemma 3.2: JL + Ramanujan-Petersson) passed a direct numerical test at p=7,11,19 (22 cases); it is still not proved here, only cited by the paper.
This is an audit of arithmetic and algebra, not a refereeing of the automorphic-forms step. Not a formal proof.
