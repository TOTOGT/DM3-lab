# Plan: Jacobi's count r4(2m) = 24 sigma(m), m odd  (2026-11-16)

STATUS: plan only. No Lean written. Nothing here is proved in Lean.
Mathlib (checkout dated 2026-07-13) has Lagrange's existence theorem (NumberTheory/SumFourSquares.lean)
but no count and no Hurwitz quaternions.

## Route: Hurwitz quaternions
H = {a+bi+cj+dk : all of a,b,c,d in Z, or all in Z+1/2}.  N(q) = a^2+b^2+c^2+d^2.  |units| = 24.

Target T: h(n) := #{q in H : N(q) = n} = 24 * sigma_odd(n)  for every n >= 1  (sigma_odd = sum of odd divisors).

Step A (checked by hand + numerically):  for n EVEN, h(n) = r4(n).
  A half-integer element has four odd numerators u_i with sum u_i^2 = 4n.  Four odd squares sum to 4 mod 8,
  but n even gives 4n = 0 mod 8.  So no half-integer elements; every element of norm n is in Z^4.
  Then for n = 2m, m odd: r4(2m) = h(2m) = 24 sigma_odd(2m) = 24 sigma(m).   (sigma_odd(2m) = sigma(m))

Step B (math standard, NOT yet re-derived by me line by line):  H is left- and right-Euclidean for N.
  Round a b^{-1} to the nearest point of the D4* lattice: squared distance <= 1/2 < 1.

Step C (standard, NOT yet re-derived): unique factorization of primitive elements up to units,
  giving h(n) = 24 * sigma_odd(n).  This is the long part (primitive counts, then sum over d^2 | n).

## Numerical evidence (Python brute force, n = 1..60, NOT a proof)
  h(n) = 24 sigma_odd(n) for all n;  half-integer count is 0 for all even n;  r4(2m) = 24 sigma(m) for all n = 2 mod 4.
  Examples: r4(6) = 96 = 24*4;  h(5) = 144 = 24*6.

## Honest scope
Finishing Jacobi does NOT finish Euler's conjecture.  The paper's real blocker is Proposition 6.1
(Ramanujan-Petersson through Jacquet-Langlands), which Mathlib does not have.
Jacobi's count is a useful standalone result, and it feeds the paper's identity R(n) = 24 sigma(m),
but the conditional theorem in Euler1747.lean stays conditional either way.

## Order of work if we proceed
1. Define the Hurwitz order as a subring of Quaternion Q and prove N multiplicative (Mathlib: Quaternion.normSq).
2. Step A in Lean (small).  3. Step B (Euclidean).  4. Step C (the bulk, likely many sessions).
Each step: hand-derive, write Lean, mark untested, you run it, fix against the compiler.
