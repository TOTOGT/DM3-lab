# Aggregate route for H31gt3: exact statement and error budget

Written 21 Nov 2026 by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. Nothing here is published. `H31gt3` and the existing chain are unchanged.

## Exact statement (EDagg.lean)
Definitions reuse `Section63.PT`, `Section63b.Pn`, `Section42.bp`, `Section51.sig`. `AggSmall m T` says
(1/(24 sigma m)) * sum over p in PT(Pn(2m)) of b_p(2m) <= T.
`AggTarget m` is `AggSmall m (2/3 - L(2m))`, where `L` is `Section63b.large_primes`' bound (`largePrimeBound`).
Compiled: `EDagg.agg_of_h31` (the per-prime hypothesis of `prop61_core` implies `AggSmall m (21/50 + E(2P/15+1))`; this is `small_primes_sum`). Axioms: propext, Classical.choice, Quot.sound. Not proved: `AggTarget m` itself, and not proved here: that `AggTarget` plus the large-prime bound closes `prop61_core` (that is the final `linarith` step of `prop61_core`, which would be re-run with `AggTarget` in place of `hS`).

## Budget (budget.py; arithmetic only, read from `Section63.final_arith` and `Section63b.large_primes`)
At the threshold n = 2m = 64^4 (u = n^(1/20) = 2.297, P = 128): the large-prime bound is L = 0.0978, so the small-prime sum must be below 2/3 - L = 0.5689. The constant 21/50 = 0.42 used in the chain bounds the main term; the room above it for the error is 0.1489, i.e. E <= 8.24e-3 in the form `b_p/(24 sigma) <= 2/(p(p-1)) + E`. The Lean chain's own cap is E <= 0.98/u^6 = 6.67e-3, so the existing hypothesis uses 81% of the available room at the threshold.
The true main sum over the 16 primes p = 3 (mod 4), p <= 127 is 0.4157 (below the 21/50 used), so the room over the true main term at the threshold is 0.1532 in total.
For larger n the allowed E_max falls like m^(-1/4) (fitted slope -0.247 to -0.2495 over n = 1e20 to 1e40). A per-prime error of size tau(m) m^(delta - 1/2)/3 therefore closes asymptotically exactly when delta < 1/4. This is an asymptotic statement; the finite threshold needs its own check.

## What averaging can and cannot do
Each b_p is a nonnegative count, so the sum has no sign cancellation. A saving over the per-prime bound must come from structure of the counts themselves (for example the same lattice points being counted for several p). Nothing in this note proves such a saving.

## Exact aggregate sums at the threshold (agg_true.py; computed, 4 values of m, not a proof)
`b_p(n)` is an elementary count: representations n = x0^2+x1^2+x2^2+x3^2 with x0+x1 and x2+x3 odd and p dividing both coordinates of one pair. With r2odd(v) = #{(a,b) : a^2+b^2 = v, a+b odd}, b_p(n) = 2 sum_v r2odd(v) r2odd(n - p^2 v) - (overlap, zero when p^2 does not divide n). `agg_true.py` evaluates this exactly, with no per-prime bound assumed.

| m | prime factors | S(m) = sum_p b_p / (24 sigma) | target T* | sum 2/(p(p-1)) | max_p (b_p/(24 sigma) - 2/(p(p-1))) |
|---|---|---|---|---|---|
| 8388611 | prime | 0.2333 | 0.5689 | 0.4157 | -4.7e-05 |
| 8388619 | prime | 0.2771 | 0.5689 | 0.4157 | -2.7e-05 |
| 8388671 | 3 primes | 0.2732 | 0.5689 | 0.4157 | -3.4e-05 |
| 8388721 | 4 primes | 0.2620 | 0.5689 | 0.4157 | -4.6e-05 |

At these four values the true sum is about half the target, and every per-prime inequality holds with no error term at all. This is evidence about the truth of AggTarget at the threshold, not a proof of it for all m. The proof obligation is a bound on a sum of r2odd convolutions, which is elementary in statement and is where an aggregate argument would have to work.
