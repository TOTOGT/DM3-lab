# ED files: Euler 1747 (n ≡ 2 mod 4), reduction to the prime-case bound

Written 21 Nov 2026 by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. Nothing here is published.

## What compiles (Lean 4.32, Mathlib from the repo's lake manifest; each file compiled in order against `StageA4o` and `Stage83`)
EDa1 (|PGL₂(F_p)| = p(p²−1)), EDa3 to EDa9 (|O_p| ≤ (p+1)/2, i.e. 2·|O_p| ≤ p+1), EDb1 to EDb4 (counting #{α : ρ(α) ∈ K_p} ≤ 8·(T_m 1_{O_p})(base)), EDb5 (P2), EDb6 (P1: α = x·(1+i)⁻¹, injective, lands in Q_m), **EDb7** (join: b_p(2m) ≤ #{α ∈ Q_m : ρ(α) ∈ K_p}), **EDb8** (assembly: `H31gt3_of_hprime`), **EDb9** (`euler_1747_of_hprime`).

`Stage83cut.lean` (not in this folder) is `Stage83.lean` with the 23 namespaces it shares with `StageA4o` dropped and `import StageA4o` added, so one file can see `Section42.bp`, `Section83.H31gt3` and the A4o results.

## The final theorem
```
theorem EDb9.euler_1747_of_hprime (hP : EDb8.HPrime) (n : ℕ) (hn4 : n % 4 = 2) :
    ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n
```
`#print axioms`: propext, Classical.choice, Quot.sound, and `Euler1747.allOk_true._native.native_decide.ax_1_1`. The last is the finite check for n < 64⁴ done with `native_decide` (the Lean compiler as a trusted step); the first three are standard. No `sorry` in EDa1, EDa3 to EDa9 or EDb1 to EDb9. (`EDa2.lean` is an unused scratch file with `sorry` and is not part of the chain.)

## What `HPrime` is
For every prime p with p ≡ 3 (mod 4) and p > 3, every choice of (x, y) in 𝔽_p with x² + y² = −1, and every prime ℓ admissible at p (odd and ≠ p): ‖T_ℓ f‖ ≤ 2√ℓ ‖f‖ for every f orthogonal to the constant function and to χ. This is the paper's Lemma 3.2 for primes (arXiv 2611.00370), the Ramanujan–Petersson-type bound. It is NOT proved here. The E-D2 route is Brandt/Eichler identification with S₂(Γ₀(p)) (Pizer), the Eichler–Shimura relation (Diamond–Shurman Thm 8.7.2) and the Weil bound.

## What to say publicly, and no more
"Euler's 1747 conjecture for n ≡ 2 mod 4 reduces, in Lean, to one named spectral hypothesis (`HPrime`) plus a finite `native_decide` check." The hypothesis was checked numerically in 82 instances according to the project's earlier files (not rechecked here). If `HPrime` were false for some admissible (p, ℓ) the theorem would be vacuous, so its truth is the open content.

## Next
E-D2a: write the one-page dependency statement (which two imported facts replace `HPrime`, with citations and what Mathlib lacks). E-E: replace `native_decide`. E-A: CI build with axiom printing. E-F: refresh LEMMA_LEDGER.md and JACOBI_PLAN.md. E-G: upstream EDa1 and EDa3 to Mathlib.
