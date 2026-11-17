# euler/lean (DM3-lab)

Independent Lean attempt at parts of Howe-Huffman-Kohlmeyer-Kruer, hexagon:2611.00370v1
(Euler's 1747 conjecture). NOT their formalization. Drafts, 2026-11-16.

| File | What it is | Status |
|---|---|---|
| EulerLean/FourSquaresMixed.lean | |Rmix| = (2/3)|R| for n = 2 mod 4 (paper eq. 2.2) | compiled; standard axioms only |
| EulerLean/Euler1747.lean | finite range (paper Prop 7.2) by native_decide; conjecture CONDITIONAL on AnalyticRange (paper Prop 6.1, a hypothesis here) | compiled; finite part uses the native_decide axiom (compiler-trusting) |
| EulerLean/HurwitzStepA.lean | step A of JACOBI_PLAN.md: no half-integer Hurwitz elements of even norm | UNTESTED, not compiled |
| EulerLean/JACOBI_PLAN.md | plan for Jacobi's count r4(2m) = 24 sigma(m) | plan only, no Lean |

Run locally against any Lean v4.32.0 + Mathlib checkout, for example:
`cd ~/Desktop/geometry && lake env lean ~/Desktop/DM3-lab/euler/lean/EulerLean/HurwitzStepA.lean`
Or in CI: Actions > "Euler (Lean kernel check)" > Run workflow.
