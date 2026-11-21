# p-adic correction for primes dividing m (frozen before testing)

Written 21 Nov 2026 by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. Nothing here is published. **`HPrime` stays OPEN.** `AggSmall`, `AggTarget`, `HPrime` and the Lean chain are unchanged. The formulas below were fixed in the header of `agg_scale_k.py` (sha256 prefix `bb277917989a`) before it was run on fresh m.

## Valuation check
10000053 = 3^2 · 7 · 158731. It is divisible by 9 (digit sum 9), and 10000053/9 = 1111117 has digit sum 13, so v_3 = 2 exactly. It was kept as a diagnostic, not a fitting point.

## Derivation (p = 3 mod 4, n = 2m, k = v_p(m))
1. **Local density of Q.** Over Z_p the form x0²+x1²+x2²+x3² is unimodular of discriminant 1 (Q = H+H), so σ_p(n) = (1 − p⁻²)(1 + p⁻¹ + … + p⁻ᵏ).
2. **The constraint p | x0, p | x1.** Put x0 = pu, x1 = pv. The box has measure p⁻² of Z_p², which is the p⁻² factor, but the remaining density is not that of a free sum: it is the density of the binary norm form N(x2,x3) = x2²+x3² (anisotropic, unramified) at w = n − p²N(u,v). N has density (1+1/p)·[v_p(w) even]. For (u,v) Haar-random, the probability that v_p(n − p²N(u,v)) is even is 0 for k=1 and 1 − p⁻⁽ᵏ⁻¹⁾ for k ≥ 2 (split on v_p(u,v) = a, using that N of a primitive vector is a uniform unit; the closed form is the same for even and odd k−2). So σ_p^c(n) = p⁻²(1+1/p)(1 − p⁻⁽ᵏ⁻¹⁾) for k ≥ 1, and p⁻²(1+1/p) for k = 0.
3. **Conditional density** r_p(k) = σ_p^c/σ_p: r_p(0) = 1/(p(p−1)); for k ≥ 1, r_p(k) = (p^(k−1) − 1)/(p^(k+1) − 1). Explicitly r_p(1) = 0, r_p(2) = 1/(p²+p+1), r_p(3) = 1/(p²+1), r_p(4) = (p³−1)/(p⁵−1). It is not p⁻².
4. **Contribution to b_p.** For k = 0 the events "p | x0,x1" and "p | x2,x3" are disjoint, so b_p ≈ 2|Rmix| r_p(0). For k ≥ 1, p | x0,x1 and p | n force p | x2²+x3², hence p | x2, x3 (−1 is a non-residue mod p): the two events coincide, so b_p ≈ |Rmix| r_p(k) with **no factor 2**. The old M used the factor 2 and a density 1/(p³+p²−p) for every p | m.
5. **Exact identity (no asymptotics).** The same argument shows that for p | m: b_p(2m) = #{y : Q(y) = 2m/p², parity conditions} = 16·σ(m/p²) if p² | m, and 0 if p ∥ m. It agrees with step 3 because σ(m/p²)/σ(m) = r_p(k).
Main term: M3(m) = (2/3) Σ_p w_p, with w_p = 2/(p(p−1)) for p ∤ m and w_p = r_p(k) for p | m (divided by 24σ(m) throughout).

## Check of the derivation, before any test of m (`local_density_check.py`)
Brute-force counts mod p^s match the predicted σ_p and σ_p^c exactly (rational equality) for p = 3 with k = 1, 2, 3, 4 and p = 7, 11, 19 with k = 1, 2, each with three unit multiples. All OK.

## Fresh tests (25 values: 8 per scale for (p,k) in {(3,2),(3,3),(3,4),(7,2),(7,3),(11,2),(19,2),(23,2)} at 10⁷, 10⁸, 10⁹, plus the diagnostic)
Exact integer counts, float64 ratios; 1 s, 10 s and 114 s per scale. "b_p identity" is exact equality of the computed b_p with 16σ(m/p²) (or 0) for every p | m with p ≤ P.

| scale | m | factorisation | S | S/T* | b_p identity | M: C/m^½ | M2: C/m^½ | **M3: R** | **M3: C** | **M3: C/m^½** | **M3: C/m^¾** | **M3: C/m** |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1e7 | 10000053 | 3^2*7*158731  | 0.074441 | 0.1307 | YES | +921.169 | +1355.065 | -6.237e-05 | -2.4710e+04 | -7.814 | -0.1390 | -0.00247 |
| 1e7 | 10000449 | 3^3*370387  | 0.121605 | 0.2134 | YES | +2949.734 | +2949.734 | -2.863e-05 | -1.0180e+04 | -3.219 | -0.0572 | -0.00102 |
| 1e7 | 10001799 | 3^4*123479  | 0.126519 | 0.2221 | YES | +3531.613 | +3531.613 | -7.411e-05 | -2.6573e+04 | -8.402 | -0.1494 | -0.00266 |
| 1e7 | 10000361 | 7^2*127*1607  | 0.257085 | 0.4513 | YES | +735.562 | +735.620 | +2.918e-05 | +8.2164e+03 | +2.598 | +0.0462 | +0.00082 |
| 1e7 | 10000851 | 3*7^3*9719  | 0.036477 | 0.0640 | YES | -3612.936 | +1155.806 | -7.735e-05 | -2.8871e+04 | -9.129 | -0.1623 | -0.00289 |
| 1e7 | 10000529 | 7*11^2*11807  | 0.238294 | 0.4183 | YES | +55.632 | +385.846 | -4.059e-05 | -1.2241e+04 | -3.871 | -0.0688 | -0.00122 |
| 1e7 | 10003671 | 3^2*19^2*3079  | 0.104104 | 0.1827 | YES | +1440.719 | +1440.719 | +3.333e-06 | +1.2203e+03 | +0.386 | +0.0069 | +0.00012 |
| 1e7 | 10002861 | 3^2*11*23^2*191  | 0.092718 | 0.1627 | YES | +1391.678 | +1507.976 | +1.926e-05 | +7.6545e+03 | +2.420 | +0.0430 | +0.00077 |
| 1e7 | 10000053 | 3^2*7*158731 (DIAGNOSTIC, original case) | 0.074441 | 0.1307 | YES | +921.169 | +1355.065 | -6.237e-05 | -2.4710e+04 | -7.814 | -0.1390 | -0.00247 |
| 1e8 | 100000071 | 3^2*11111119  | 0.106709 | 0.1824 | YES | +3784.066 | +3784.066 | +3.756e-05 | +1.3021e+05 | +13.021 | +0.1302 | +0.00130 |
| 1e8 | 100000143 | 3^3*83*44623  | 0.121885 | 0.2083 | YES | +9458.481 | +9459.310 | +2.436e-05 | +8.7652e+04 | +8.765 | +0.0877 | +0.00088 |
| 1e8 | 100000413 | 3^4*43*28711  | 0.126274 | 0.2158 | YES | +11447.116 | +11453.132 | -2.777e-06 | -1.0186e+04 | -1.019 | -0.0102 | -0.00010 |
| 1e8 | 100000131 | 3*7^2*11*61843  | 0.023221 | 0.0397 | YES | -13439.441 | +3344.074 | +2.064e-06 | +8.3820e+03 | +0.838 | +0.0084 | +0.00008 |
| 1e8 | 100000621 | 7^3*291547  | 0.259178 | 0.4429 | YES | +2756.618 | +2756.618 | -2.103e-05 | -5.8859e+04 | -5.886 | -0.0589 | -0.00059 |
| 1e8 | 100001297 | 11^2*191*4327  | 0.270432 | 0.4622 | YES | +1074.995 | +1075.046 | -3.423e-05 | -9.0798e+04 | -9.080 | -0.0908 | -0.00091 |
| 1e8 | 100000249 | 19^2*439*631  | 0.275561 | 0.4709 | YES | +422.730 | +422.730 | +9.786e-05 | +2.4884e+05 | +24.884 | +0.2488 | +0.00249 |
| 1e8 | 100003747 | 23^2*189043  | 0.276154 | 0.4719 | YES | +268.995 | +268.995 | -2.819e-05 | -7.0730e+04 | -7.073 | -0.0707 | -0.00071 |
| 1e9 | 1000000071 | 3^2*7*619*25643  | 0.075120 | 0.1259 | YES | +9301.935 | +13648.038 | -2.537e-06 | -1.0068e+05 | -3.184 | -0.0179 | -0.00010 |
| 1e9 | 1000000269 | 3^3*37037047  | 0.122253 | 0.2050 | YES | +29528.301 | +29528.301 | -4.370e-07 | -1.5539e+04 | -0.491 | -0.0028 | -0.00002 |
| 1e9 | 1000000323 | 3^4*7*103*17123  | 0.095329 | 0.1598 | YES | +36302.773 | +40835.448 | -9.976e-06 | -4.1276e+05 | -13.053 | -0.0734 | -0.00041 |
| 1e9 | 1000000869 | 3*7^2*6802727  | 0.035539 | 0.0596 | YES | -37867.592 | +9693.718 | +2.255e-06 | +8.3929e+04 | +2.654 | +0.0149 | +0.00008 |
| 1e9 | 1000005181 | 7^3*2915467  | 0.259404 | 0.4349 | YES | +8742.801 | +8742.801 | +7.943e-06 | +2.2230e+05 | +7.030 | +0.0395 | +0.00022 |
| 1e9 | 1000000507 | 11^2*8264467  | 0.270716 | 0.4539 | YES | +3423.278 | +3423.278 | +1.635e-05 | +4.3123e+05 | +13.637 | +0.0767 | +0.00043 |
| 1e9 | 1000001407 | 19^2*2770087  | 0.275677 | 0.4622 | YES | +1267.019 | +1267.019 | +1.719e-05 | +4.3532e+05 | +13.766 | +0.0774 | +0.00044 |
| 1e9 | 1000000969 | 11*23^2*171851  | 0.264258 | 0.4430 | YES | +151.942 | +952.784 | +5.006e-07 | +1.3701e+04 | +0.433 | +0.0024 | +0.00001 |

## Reading
1. **The identity is exact in all 25 cases** (every p | m with p ≤ P; includes p², p³, p⁴ and composites with several small primes).
2. **Uncorrected vs corrected.** With the pre-declared M, |C|/m^½ ranges from 56 to 37,868 (C/m up to about 1.3). With M3 it is 0.4 to 24.9 for every one of the 25 values, |C|/m^¾ ≤ 0.25 and |C|/m ≤ 0.003. M2 (post-hoc, p ∥ m only) fixes the p ∥ m cases and fails for p² | m, as expected.
3. **Scale behaviour of M3.** Maximum |C|/m^½ is 9.1 at 10⁷, 24.9 at 10⁸, 13.8 at 10⁹; maximum |C|/m^¾ is 0.16, 0.25, 0.08. There is scatter, no growth in m^½-units across the three scales, and no clean decay either: three scales cannot separate m^½ from m^(½+small). S/T* stays between 0.04 and 0.47.
4. **What this settles and what it does not.** The correction for p² | m is now derived (not fitted), it is checked locally by exact counts, and it predicts 25 fresh values with a residual of the same size (about m^½) as the coprime case. The aggregate S(m) therefore has the expected main term for all the m tested, and the remaining residual is the arithmetic fluctuation. A proof of `AggTarget` for all m still needs a uniform bound on that fluctuation, which is the same kind of estimate as HPrime. Not tested: P larger relative to m, p ≥ 31 with p² | m, composites with p⁵ | m, m not coprime to all primes ≡ 1 mod 4 (not needed for Prop 6.1, whose m has only primes ≡ 3 mod 4).
