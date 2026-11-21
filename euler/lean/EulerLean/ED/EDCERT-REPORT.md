# EDcert: kernel-checked finite range for Euler 1747 (verification commit, 21 Nov 2026)

**Scope.** Replaces the `native_decide` proof of the finite range n < 64⁴ with a kernel-checked certificate and adds `EDb9k.euler_1747_of_hprime_k`, the same conditional theorem as `EDb9.euler_1747_of_hprime` without `Lean.ofReduceBool`. `HPrime`, `Stage83cut.lean` and every earlier declaration are unchanged (the old `allOk_true` and `EDb9.euler_1747_of_hprime` still exist and still carry the native axiom).

## Axiom audit (`#print axioms`, Lean 4.32.0, Mathlib rev 81a5d257)
| Declaration | Axioms |
|---|---|
| `EDcert.good_of_sq_add_sq` | propext, Classical.choice, Quot.sound |
| `EDcert.chunk_sound` | propext, Classical.choice, Quot.sound |
| `EDcert.euler_finite_k` | propext, Classical.choice, Quot.sound |
| `EDcert.euler_1747_of_H31gt3_k` | propext, Classical.choice, Quot.sound |
| `EDb9k.euler_1747_of_hprime_k` | propext, Classical.choice, Quot.sound |

No `sorry`, no `native_decide`, no new axioms; the only hypothesis of the final theorem is the explicit `EDb8.HPrime`.
Verification class: kernel-reducible computation (`decide +kernel`, proof term `of_decide_eq_true (Eq.refl true)`) with a proved soundness theorem. No external evaluator is trusted.

## What was proved
Statement preserved: every n ≡ 2 (mod 4) with n < 64⁴ is a + b with `EulerGood a`, `EulerGood b`, and min(a, b) ≤ 313 (`EDcert.euler_finite_k`; same conclusion as `Euler1747.euler_finite`).
* `good_of_sq_add_sq`: gcd(x, y) = 1 and x² + y² odd ⇒ `EulerGood (x² + y²)`. Proof: a prime p | x² + y² with p ∤ x gives (y/x)² = −1 in ZMod p, so p % 4 ≠ 3 (`ZMod.exists_sq_eq_neg_one_iff`); p | x forces p | y, contradicting gcd = 1. The prime and congruence restrictions are in this lemma, not in the computation.
* `chunk_sound`: if `chunkOk c = true` then every n ≡ 2 mod 4 in [c·2¹⁶, (c+1)·2¹⁶) equals a + b with a one of 43 explicit candidates (each certified by a primitive two-square representation, `candsL_good`) and b a certified primitive sum of two squares. Soundness is independent of how the pairs (x, y) are enumerated; the enumeration only decides whether the check succeeds.
* `chunkOk c`: the kernel builds, with GMP bit operations, the bitmask of all odd primitive x² + y² in the window, ORs its shifts by the candidates and compares with the mask of the required n.
* 256 theorems `chunk_c`, c < 256, cover n < 2²⁴ = 64⁴ (`chunks_ok`; the bound c < 256 is derived from n < 64⁴ in `euler_finite_k`). All 256 are present: `chunks_ok` is closed by `interval_cases` with one named theorem per case.
* `euler_1747_of_analytic_range_k` is a copy of `Euler1747.euler_1747_of_analytic_range` with `euler_finite_k` in place of `euler_finite`; `euler_1747_of_H31gt3_k` rebuilds `Section83.euler_1747_of_H31gt3` from `Section65.analytic_range_of`, `Section65.hr2`, `Section70.h31_of_ndvd`, `Section81.hjac`.

## Independent check of the finite statement (not part of the proof)
`finite_check.py` sieves all n < 64⁴ separately: 4,194,304 values of n ≡ 2 mod 4, 0 uncovered, 43 candidates ending at 313.

## Build notes
Plain kernel evaluation of the old test (`goodB` with `primeFactorsList`) did not finish 20 values in 5 minutes, hence the certificate design. One chunk takes about 10 s. Memory grows during a file (to about 5 GB for 32 chunks), and two files in parallel were killed, so build sequentially:
`./build_cert_seq.sh EDcertD0 … EDcertD13 EDcertCore EDcert EDb9k` after `EDcertDefs` and `EDcertC1` (chunks 32–63). Total about 45 minutes (see `logs/cert_build.log`). Module order: EDcertDefs (core Lean only), EDcertC1 and EDcertD0–D13 (chunk theorems), EDcertCore (soundness, imports Stage83cut), EDcert, EDb9k (imports EDb8).
Not done: these modules are not yet in the lakefile or the ED-layer CI workflow.
