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
