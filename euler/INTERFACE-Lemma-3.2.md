# Interface note: the one spectral input behind our Lean reduction of Euler's 1747 conjecture

Draft, 20 Nov 2026. For readers who work on modular forms, Eichler-Shimura or Jacquet-Langlands and want to know what would have to be supplied, without reading the Lean files. Nothing here claims a proof of the lemma below.

## 1. Setting (everything in this section is defined and used in Lean)

- B = (-1,-1)_Q, the definite quaternion algebra ramified at {2, infinity}. O is the Hurwitz order, a maximal order. O^x has 24 elements.
- p is an odd prime (the Lean statement uses p = 3 mod 4). O/pO is isomorphic to M_2(F_p). Gamma_p is the image of O^x in PGL_2(F_p); |Gamma_p| = 12.
- Y_p = Gamma_p \ PGL_2(F_p), with |Y_p| = p(p^2-1)/12. L^2(Y_p) carries the counting inner product.
- For odd m with p not dividing m, U_m sums the action of the Hurwitz quaternions of norm m (there are 24 sigma(m)) through O/pO = M_2(F_p), and T_m = U_m / 24.
- Proved in Lean (kernel-checked, standard axioms only): T_m is self-adjoint; the odd T_m commute; T_m T_l = T_{lm} + l T_{m/l} summed over common divisors, i.e. the usual Hecke relations; T_mn = T_m T_n for coprime m, n; T_m 1 = sigma(m) 1; T_m chi = (m/p) sigma(m) chi, where chi is the quadratic character of det.

## 1a. The adelic form (hand-derived, not in Lean)

Let K_p be the kernel of O-hat^x -> GL_2(F_p) taken at p (full local units O_l^x at every other prime l), and Z the central Q-hat^x. Since O has class number one, B-hat^x = B^x O-hat^x, so

    B^x \ B-hat^x / (Z K_p)  =  O^x \ GL_2(F_p) / F_p^x  =  Gamma_p \ PGL_2(F_p)  =  Y_p.

The cardinality p(p^2-1)/12 agrees. So L^2(Y_p) is the space of weight-2, trivial-character algebraic modular forms on B of level K_p, in the sense used by the Imperial FLT blueprint (functions on B^x \ (B (x) A^infty)^x, invariant under the centre and a compact open subgroup). T_m is the Hecke operator at the primes dividing m. If those definitions reach Mathlib, our L^2(Y_p) is an instance of theirs, and Section 1 is a concrete test case for their Hecke API. This identification is the paper's equation (3.5); we derived it by hand above and have not formalized it.

## 2. The statement we need (Lemma 3.2 of the source paper)

For odd m with p not dividing m, and every f in L^2(Y_p) orthogonal to span{1, chi}:

    || T_m f || <= tau(m) sqrt(m) || f ||.

## 3. How it is meant to follow from standard results (this is read, not verified)

(a) The one-dimensional automorphic representations of B^x that have a vector fixed at this level lie in span{1, chi}.
(b) Every other constituent of L^2(Y_p) corresponds under Jacquet-Langlands to a cuspidal weight-2 newform whose level is supported on 2 and p, with Hecke eigenvalue a_l at each prime l not dividing 2p. The exact level and nebentypus must be confirmed; we have not done so.
(c) The Ramanujan-Petersson bound |a_l| <= 2 sqrt(l) for weight 2. It gives |a_m| <= tau(m) sqrt(m) for m coprime to the level, which is the bound above. The source paper cites Deligne. My recollection, not checked, is that weight 2 may need only Weil's bound for curves via Eichler-Shimura.

## 4. What is and is not in Lean

- In Lean: section 1; the one-vector bridge (a bound on <h, T h> gives a pointwise bound on T f); and the conditional theorem Section83.euler_1747_of_H31gt3.
- Not in Lean, and not claimed: (a), (b), (c); the identification of the class set of B with Y_p (equation (3.5) of the source paper); the step from Lemma 3.2 to H31gt3.
- H31gt3 is the paper's Proposition 3.1 for primes p > 3: an inequality about a count b_p, not the eigenvalue bound itself. The paper derives it from Lemma 3.2. That derivation is the remaining work on our side. It is not a one-line step.

## 5. Evidence it is true in the tested range

Computed: the Hecke operators were built from the quaternions directly for p = 3, 7, 11, 19 and many odd m. Lemma 3.2 had 0 violations in 82 instances (m = 1 is the trivial equality case and is counted separately). The checks are in `audit_lemma32.py`, and the status is recorded in `LEMMA_LEDGER.md`. This supports the outcome only; it does not prove the lemma.

## 6. Not claimed

No claim of a proof of the Ramanujan-Petersson bound, of Jacquet-Langlands, or of Euler's 1747 conjecture. The Euler result in Lean is conditional on H31gt3.
