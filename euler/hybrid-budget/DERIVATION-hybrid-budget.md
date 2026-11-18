# Conditional hybrid budget for Euler 1747

Prepared 18 November 2026. This is a paper derivation with a Python exact-arithmetic certificate. No new Lean theorem was compiled for this package. The missing uniform estimate and the additional finite verification for weakened exponents remain open.

## Scope and notation

Let n = 2m, where m > 0 is odd and every prime factor of m is 3 modulo 4. Put R = 24 sigma(m), and let S(n) be the sum of b_p(n)/R over primes p <= n with p = 3 modulo 4. All counts are signed and ordered, matching the Lean definitions. Let M(n) be Section62.Mn n.

Assume C >= 0 and 1/2 <= beta < 3/5. For EVERY qualifying m and EVERY prime p satisfying 3 < p <= P(n), p = 3 modulo 4 and p not dividing m, require the pointwise estimate

    b_p(2m)/(24 sigma(m))
        <= 2/[p(p-1)] + C tau(m) m^beta/[3 sigma(m)].                 (H)

The quadratic-form bound on h_p = 1_{O_p} - mu_p 1, mu_p = 6/[p(p-1)], is sufficient for (H) once the concrete quotient, operator, constancy and counting bridges have been proved. This package assumes (H) at that interface. It does not prove the quadratic-form bound or instantiate Bridge.lean for the concrete Hecke action.

The p dividing m branch already has the main-term bound, and the checked p = 3 bound contributes at most 1/3. Both can therefore be included in the small-prime main-term sum. The factor 1 - mu_p from the quadratic-form implication is bounded above by 1 when the error bound is nonnegative.

For beta = 1/2 and C = 1, (H) has the existing H31gt3 bound. Other choices or moving cutoffs require a generalized analytic assembly lemma. The hypothesis covers an infinite family of m,p. A finite list of matrix calculations does not provide it.

## 1. Exact source alignment

Source snapshots were read from TOTOGT/DM3-lab at commit b9ca843a95365fb08f2a5e6c53310aaaba59a651 (docs83).

- Section6Arithmetic.final_sum_eq and final_sum_lt verify the original rational total 21235493/33177600 < 2/3. The displayed expression starts with 21/50, followed by two positive remainders. Thus subtracting 21/50 leaves the exact budget 37/150.
- Section51.lemma51_first gives tau(m)*m/sigma(m) <= (23/10)*m^(1/5).
- Section62.Mn_le gives M(n) <= (11/5)*n^(1/5).
- Section5.prime_count_bound gives 15*count <= 2P + 15 for primes 3 < p <= P with p = 3 modulo 4.
- Section5.prime_tail gives sum_{P<p<=K} 1/p^2 <= 2/(15P) + 2/P^2 for NATURAL P >= 3. Its endpoint is strictly greater than P.
- Section5.five_four bounds the complete small-prime main-term sum by 21/50.
- Section61.small_primes_sum gives 21/50 + E*(2P/15 + 1) under the corresponding pointwise hypotheses and E >= 0.
- Section62b.large_primes gives (44/15)*n^(1/5)*[2/(15P) + 2/P^2 + (2 sqrt(n)/15 + 1)/n].
- Section63.final_arith and Section63b.prop61_core are wired to the ORIGINAL cutoff floor(2*n^(1/4)). They do not automatically accept a new beta or cutoff. In their rational proof, E <= (49/50)*n^(-3/10) is a conservative bound for the original spectral error. We derive the new beta dependence directly from lemma51_first.
- Section64.euler_conditional packages the original analytic estimate with Sufficiency.sufficiency. Section70 supplies the p dividing m case; Stage83 also supplies p = 3.

Source links

https://github.com/TOTOGT/DM3-lab/blob/b9ca843a95365fb08f2a5e6c53310aaaba59a651/euler/lean/EulerLean/Section6Arithmetic.lean
https://github.com/TOTOGT/DM3-lab/blob/b9ca843a95365fb08f2a5e6c53310aaaba59a651/euler/lean/EulerLean/Stage63b.lean
https://github.com/TOTOGT/DM3-lab/blob/b9ca843a95365fb08f2a5e6c53310aaaba59a651/euler/lean/EulerLean/Stage64.lean
https://github.com/TOTOGT/DM3-lab/blob/b9ca843a95365fb08f2a5e6c53310aaaba59a651/euler/lean/EulerLean/Stage70.lean
https://github.com/TOTOGT/DM3-lab/blob/b9ca843a95365fb08f2a5e6c53310aaaba59a651/euler/lean/EulerLean/Stage83.lean
https://hexagonmath.org/pdf/2611.00370v1

## 2. A free NATURAL cutoff

Use p <= P for the small range and p > P for the tail. If the plan uses p < p0 and p >= p0 with integer p0, set P = p0 - 1. Using the same endpoint symbol for both conventions introduces a boundary error.

The normalized individual geometric estimate is

    b_p(n)/R <= (4/3)*M(n)*(1/p^2 + 1/n)
              <= (44/15)*n^(1/5)*(1/p^2 + 1/n).

The coefficient is 44/15. Substituting M(n) again after this step double-counts its contribution. Only primes p^2 <= n can have a nonzero bad mixed representation, since each mixed coordinate pair has positive norm. The prime count term is therefore bounded using sqrt(n), giving

    E2(n,P) = (44/15)*n^(1/5)
                * [2/(15P) + 2/P^2 + 2/(15 sqrt(n)) + 1/n].        (1)

From lemma51_first,

    C*tau(m)*m^beta/[3 sigma(m)]
       = (C/3)*[tau(m)*m/sigma(m)]*m^(beta-1)
       <= (23C/30)*m^(beta-4/5).

Consequently

    E1(n,P) = (23C/30)*(n/2)^(beta-4/5)*(2P/15 + 1).               (2)

For beta = 1/2 the exponent beta - 4/5 is -3/10. Equations (1)-(2) yield the conditional bound

    S(n) <= 21/50 + E1(n,P) + E2(n,P).                            (3)

This includes every prime in the finite support p <= n. The 21/50 main-term bound can include extra positive main terms from beyond P, which only enlarges the upper bound.

## 3. Why the moving cutoff works

Ignoring lower-order terms, write

    A = (23C/225)*2^(4/5-beta),   D = 88/225.

The leading errors in (3) are

    A*P*n^(beta-4/5) + D*n^(1/5)/P.

For C > 0 they balance at P = sqrt(D/A)*n^((1-beta)/2). We choose the simpler explicit rule

    a = (1-beta)/2,
    P(n) = floor(2*n^a).                                         (4)

This choice has no per-n numerical optimizer. It need not be optimal. It is sufficient for the certificates below.

At beta = 11/20 (0.55), a = 9/40. The leading tail n^(1/5)/P decays as n^(-1/40). The separate n^(1/5)/P^2 term decays as n^(-1/4). In particular, n^(1/5 - 2*(9/40)) = n^(-1/4), NOT n^(-1/20). The matching leading spectral term also decays as n^(-1/40).

A cutoff o(n^(1/5)) makes this displayed tail upper bound grow. For a power cutoff, decay of the leading pair is possible in the interval 1/5 < a < 4/5 - beta, which is nonempty when beta < 3/5.

## 4. Floor correction and a monotone envelope

Set rho = 127/128. Provided 2*n^a >= 128,

    2*rho*n^a <= P(n) <= 2*n^a.

The lower bound follows from floor(t) >= t-1 >= rho*t for t >= 128. Substituting these two inequalities into (1)-(2), define e = (beta - 3/5)/2 and f = beta - 4/5. Then

    E1 <= (46C/225)*2^(4/5-beta)*n^e
           + (23C/30)*2^(4/5-beta)*n^f,

    E2 <= [44/(225*rho)]*n^e
           + [22/(15*rho^2)]*n^f
           + (88/225)*n^(-3/10) + (44/15)*n^(-4/5).

Thus define

    U(n) = 21/50
       + [(46C/225)*2^(4/5-beta) + 44/(225*rho)]*n^e
       + [(23C/30)*2^(4/5-beta) + 22/(15*rho^2)]*n^f
       + (88/225)*n^(-3/10) + (44/15)*n^(-4/5).                   (5)

For C >= 0 and 1/2 <= beta < 3/5, all coefficients are positive and every displayed exponent of n is negative. Therefore U(n) decreases for positive n. Also n^a increases, so the floor condition persists beyond any certified n0. Checking U(n0) < 2/3 and 2*n0^a >= 128 certifies (3) < 2/3 for EVERY n >= n0 under (H). This monotone envelope avoids the jumps in the actual floor cutoff.

At beta = 3/5, C = 1, even the leading pair obstructs this budget. For any positive real P, AM-GM gives a lower bound 2*sqrt(A*D). Since 2^(1/5) > 1,

    4*A*D > 4*(23/225)*(88/225) > (37/150)^2.

The verifier checks the last rational comparison. This obstructs this particular sufficient estimate, not the conjecture or every possible argument.

## 5. Exact certificates

All displayed decimal bounds in this section are rounded UP from rational certificates. No floating-point calculation is used by the verifier.

For C = 1 and beta = 1/2, (5) at n0 = 64^4 has rational upper bound at most 0.63456694 < 2/3, including the floor correction. This is a separate, slightly sharper majorant than the original paper's rational total. The verifier also reproduces the original total independently

    21/50
      + (23/30)*(5/4)*(4/9)*(4/15 + 1/64)
      + (44/15)*(4/9)*(1/15 + 19/(30*64) + 1/64^3)
    = 21235493/33177600,

and checks its exact strict margin 882907/33177600 below 2/3. The supporting radical inequalities are certified by integer powers. The paper's argument uses no floating-point step here.

For C = 1 and beta = 11/20, at n0 = 10^11 the rational bounds, displayed with upward rounding, give

    E1 <= 0.13069354,
    E2 <= 0.10748027,
    U(n0) <= 0.65817380 < 2/3.

The displayed rounded E1 and E2 may sum to a slightly larger displayed number than the separately rounded total. The underlying calculations use exact Fractions throughout.

Additional sufficient thresholds for C = 1 and rule (4)

| beta | certified n0 | upward-rounded U(n0) |
|---|---:|---:|
| 1/2 | 64^4 | 0.63456694 |
| 11/20 | 10^11 | 0.65817380 |
| 14/25 | 10^13 | 0.66286342 |
| 57/100 | 10^17 | 0.66315767 |
| 29/50 | 10^25 | 0.66474900 |
| 59/100 | 10^49 | 0.66663975 |

These are sufficient thresholds. The script tests decade endpoints, and does not claim a smallest n0 or a globally optimal cutoff.

## 6. Exact finite-interval count and the Lean interface

The number of positive integers n <= B with n = 2 modulo 4 is floor((B+2)/4). Hence the number in (64^4,N] is

    max(0, floor((N+2)/4) - 4,194,304).

For N = 10^11 this is exactly 24,995,805,696. This is the full residue-class count before the factor reduction. The number of reduced hard cases has not been certified here. Certifying a stronger theorem for every n in this interval is one option; a verified reduction can restrict the extra certificate to the qualifying m. This package supplies neither finite check nor a runtime or feasibility estimate for it. The extra interval requires direct witnesses or another checked argument independently of the hypothetical analytic estimate.

Sufficiency.sufficiency has the integer hypothesis

    sum over primes p <= n, p = 3 mod 4 of bp p n < card(Rmix n).

For qualifying n = 2m, HJac and mixed_count give card(Rmix n) = 16 sigma(m) = (2/3)R. Since R > 0, multiply S(n) < 2/3 by R to obtain exactly that hypothesis. The interface is unchanged.

A moving-cutoff proof needs a generalized replacement for prop61_core and then an analytic-range assembly at its explicit n0. Reusing Section63.final_arith verbatim will not prove the beta = 11/20 case. The old H31gt3 binder is tied to floor(2*n^(1/4)); the new sufficient hypothesis (H) uses (4). For beta >= 1/2 and n >= 1 the new cutoff is no larger than the old one, but the exponent and error bound still differ.

No full conjecture proof follows from this package. The uniform estimate (H) remains hypothetical, and beta = 11/20 also requires the extra finite certificate. A beta below 1/2 would be a stronger spectral estimate when m > 1. A bound for this one test vector is sufficient, and its necessity or equivalence to the full operator-norm theorem has not been established.

## 7. Reproduce the certificate

From the extracted package directory run

    python3 certify_budget.py

Only the Python standard library is used. certificate-output.txt contains the output produced for this package.

For each rational power b^(r/s), the verifier uses integer comparisons to find a rational upper bound u with u^s >= b^r. It checks this inequality exactly before using u. All errors and coefficients in (5) are nonnegative, so replacing each power by its upper bound preserves the final upper bound. Decimal output is rounded upward by integer division. The program verifies the endpoint arithmetic; the all-n extension is the monotonicity proof in section 4, awaiting Lean formalization.
