# Aggregate scaling test: does S(m) have room to replace HPrime?

Written 21 Nov 2026 by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. Nothing here is published. **`HPrime` stays OPEN.** `AggSmall`, `AggTarget`, `HPrime` and the Lean chain are unchanged.

## Definitions (fixed in the header of `agg_scale.py` before the runs)
- S(m) = (1/(24 sigma(m))) * sum over primes p = 3 mod 4, p <= P=floor(2(2m)^(1/4)), of b_p(2m)  (this is `EDagg.AggSmall`'s sum, evaluated exactly).
- M(m) = (2/3) * sum_p 2*delta_p, with delta_p = 1/(p(p-1)) for p not dividing m and 1/(p^3+p^2-p) for p dividing m. This comes from local densities mod p and the fact |Rmix| = (2/3)(24 sigma). It was not adjusted after seeing results.
- R = S - M (dimensionless). C = 24 sigma(m) R (the same residual as a count of representations). The normalised errors below use C, since C/m^(1/2) is the Ramanujan-size comparison; R·m^(1/4) is the dimensionless residual against the budget exponent. S/T* is the ratio to the `AggTarget` bound.
- Exact integer counts (int64, no sampling); ratios in float64. Tables built in 0 to 19 s, each m in 0 to 7 s on 2 cores. The code was checked against the independent convolution `agg_true.py` at m=8388611 (S = 0.233301 vs 0.2333).

## Results with the pre-declared M (15 values of m, five per scale)
| scale | m | factors (primes <= P marked) | S | M | R=S-M | C=24σR | C/m^½ | C/m^¾ | C/m | R·m^¼ | S/T* |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1e7 | 10000009 | 23·434783 (small: 23) | 0.274535 | 0.274660 | -1.245e-04 | -3.1180e+04 | -9.860 | -0.1753 | -0.00312 | -0.0070 | 0.4819 |
| 1e7 | 10000019 | 10000019 | 0.277265 | 0.277190 | +7.567e-05 | +1.8162e+04 | +5.743 | +0.1021 | +0.00182 | +0.0043 | 0.4867 |
| 1e7 | 10000047 | 3·911·3659 (small: 3) | 0.054962 | 0.095371 | -4.041e-02 | -1.2949e+07 | -4094.729 | -72.8156 | -1.29486 | -2.2724 | 0.0965 |
| 1e7 | 10000053 | 3^2·7·158731 (small: 3,7) | 0.074441 | 0.067089 | +7.352e-03 | +2.9130e+06 | +921.169 | +16.3809 | +0.29130 | +0.4135 | 0.1307 |
| 1e7 | 10000057 | 79·126583 (small: 79) | 0.276918 | 0.276976 | -5.757e-05 | -1.3992e+04 | -4.425 | -0.0787 | -0.00140 | -0.0032 | 0.4861 |
| 1e8 | 100000007 | 100000007 | 0.277604 | 0.277612 | -8.227e-06 | -1.9745e+04 | -1.975 | -0.0197 | -0.00020 | -0.0008 | 0.4744 |
| 1e8 | 100000013 | 827·120919 | 0.277618 | 0.277612 | +5.874e-06 | +1.4115e+04 | +1.412 | +0.0141 | +0.00014 | +0.0006 | 0.4744 |
| 1e8 | 100000031 | 283·307·1151 | 0.277601 | 0.277612 | -1.102e-05 | -2.6644e+04 | -2.664 | -0.0266 | -0.00027 | -0.0011 | 0.4744 |
| 1e8 | 100000039 | 100000039 | 0.277600 | 0.277612 | -1.250e-05 | -3.0006e+04 | -3.001 | -0.0300 | -0.00030 | -0.0013 | 0.4744 |
| 1e8 | 100000041 | 3·33333347 (small: 3) | 0.055422 | 0.095794 | -4.037e-02 | -1.2919e+08 | -12918.866 | -129.1886 | -1.29189 | -4.0371 | 0.0947 |
| 1e9 | 1000000003 | 23·307·141623 (small: 23,307) | 0.275149 | 0.275265 | -1.161e-04 | -2.9177e+06 | -92.264 | -0.5188 | -0.00292 | -0.0207 | 0.4613 |
| 1e9 | 1000000007 | 1000000007 | 0.277825 | 0.277809 | +1.615e-05 | +3.8754e+05 | +12.255 | +0.0689 | +0.00039 | +0.0029 | 0.4658 |
| 1e9 | 1000000013 | 7699·129887 | 0.277800 | 0.277809 | -8.273e-06 | -1.9858e+05 | -6.280 | -0.0353 | -0.00020 | -0.0015 | 0.4657 |
| 1e9 | 1000000057 | 7·142857151 (small: 7) | 0.246052 | 0.249526 | -3.474e-03 | -9.5280e+07 | -3013.007 | -16.9434 | -0.09528 | -0.6177 | 0.4125 |
| 1e9 | 1000000067 | 11·151·602047 (small: 11,151) | 0.265631 | 0.266554 | -9.237e-04 | -2.4345e+07 | -769.851 | -4.3292 | -0.02434 | -0.1643 | 0.4453 |

## What the pre-declared M gets wrong
M assigns a nonzero density to a prime p dividing m. That is wrong. For p = 3 mod 4: if p divides x0, x1 and n = sum of squares, then p divides x2^2+x3^2, so p divides x2, x3 (-1 is a non-residue), so p^2 divides n. Hence **b_p(n) = 0 whenever v_p(m) = 1**. This is elementary and checked below (b_p = 0 for every such p). The error in M is exactly those small terms: for 3 | m it is about 0.04, which is why m = 10000047, 10000053, 100000041, 1000000057 and 1000000067 have R between about 9e-4 and 4e-2 in absolute value in the table. For large p dividing m the error is tiny (m = 10000009 has R = -1.2e-4, the size of the p = 23 term).

## Post-hoc diagnostic (written after seeing the above; shown separately, does not replace M)
M2 sets delta_p = 0 for v_p(m) = 1 and keeps the pre-declared delta_p otherwise (`agg_scale_posthoc.py`).

| m | factors | b_p for p dividing m | S | M2 | C2 | C2/m^½ | C2/m^¾ | C2/m |
|---|---|---|---|---|---|---|---|---|
| 10000047 | 3·911·3659 | b_3 = 0 | 0.054962 | 0.054967 | -1.616e+03 | -0.511 | -0.0091 | -0.00016 |
| 10000053 | 3²·7·158731 | b_3 = 20,317,696; b_7 = 0 | 0.074441 | 0.063625 | +4.285e+06 | +1355.1 | +24.10 | +0.4285 |
| 100000041 | 3·33333347 | b_3 = 0 | 0.055422 | 0.055390 | +1.043e+05 | +10.43 | +0.1043 | +0.00104 |
| 1000000003 | 23·307·141623 | b_23 = b_307 = 0 | 0.275149 | 0.275159 | -2.731e+05 | -8.635 | -0.0486 | -0.00027 |
| 1000000057 | 7·142857151 | b_7 = 0 | 0.246052 | 0.246063 | -2.889e+05 | -9.136 | -0.0514 | -0.00029 |
| 1000000067 | 11·151·602047 | b_11 = b_151 = 0 | 0.265631 | 0.265629 | +5.140e+04 | +1.626 | +0.0091 | +0.00005 |

The one failure, m = 10000053, has 3^2 | m: there b_3 is large and M2 keeps the unjustified pre-declared density. The correct density when p^2 | m needs the p-adic computation and is not done here.

## Reading
1. **Where the main term is valid** (no p <= P with p | m, or p | m with v_p = 1 under M2), the residual is of size about sqrt(m) with a small constant: |C|/m^(1/2) is 0.5 to 12.3 across the three scales, with no growth from 10^7 to 10^9 (at 10^8 it is 1.4 to 3.0 for the four prime m; at 10^9, 6.3 to 12.3 for the two prime m, 1.6 to 9.1 for the three composite m under M2). Equivalently |C|/m^(3/4) is at most 0.18 and C/m is at most about 3e-3.
2. **The dimensionless R**: 1e-4 at 10^7, 1e-5 at 10^8 and 10^9. R·m^(1/4) stays below 0.02. The budget needs the aggregate error to fall faster than m^(-1/4) (allowed E_max falls like m^(-1/4); see AGG-BUDGET.md), and the observed error is far inside it.
3. **S/T***: 0.41 to 0.49 for the m with p=3 not dividing m (0.09 to 0.13 when 3 divides m, where the sum is smaller). Always well below 1.
4. **What this does and does not show.** The residual looks like square-root cancellation, i.e. Ramanujan-size, and there is room: the budget tolerates about m^(3/4), the data show about m^(1/2). Fifteen values at three scales support the aggregate estimate being true with room to spare. They do not prove it, and they do not show that a proof can avoid spectral input: a bound for C(m) uniformly in m and in p up to 2(2m)^(1/4) is a bound on sums of r2·r2 convolutions with congruence conditions, which is the same kind of estimate (Kloosterman/Weil type) that HPrime encodes. The route is worth pursuing as an exact elementary statement; whether an elementary proof of the needed power saving exists is open.
5. **Not tested**: m divisible by p^2 for p <= P beyond one example; larger P relative to m; m with many small prime factors; any claim for all m.
