# Splitting transport review

2026-11-25. Fresh base main 01c4210aed1c422eae8530dc8b8c2e8e48bec378.
Branch lane/splitting-review-01c4210. No tracked AGENTS.md was present.

The f963c26 snapshot in the task is superseded. Current EDc7 contains rho_conj,
Gam_conj, chiP_conj and transport, with SectionA4e rhoT qualifiers.
The theorem-local hc binder is used directly. The formerly failing source
requires no further repair on current main.

Public CI evidence rechecked directly:
EDc8 run 45534909558, job 138939018835, tested commit
59af1de199f6eafd908c7be737478a68b3c3c3e8. Assert pins and Compile chain and gate
both succeeded. The source files and pin files in the EDc8 import closure
have not changed between this tested commit and current main. The exact
seven-declaration gate permits only propext, Classical.choice, Quot.sound
and rejects sorryAx. Individual full compiler reports were not read this run;
do not reinterpret the gate as evidence that every report contains all three.
The EDc7 success is independently recorded at 8de758f, run 45532991247.

The existing statements cover the lane's requested content:
- exists_red_conjugator: for p prime, 2 nonzero and any two splitting pairs
  each satisfying x²+y²=-1, some invertible c conjugates red on every
  rational quaternion. No conjugacy or spectral hypothesis.
- EDc7.transport: from that conjugacy, an equivalence of the rightRel
  coset types preserves the determinant character and intertwines U_n
  for all n not divisible by p. No normality of Gamma is assumed.
- Lmap_inner: pullback by the inverse of any such finite equivalence
  preserves the complex counting inner product.
- Lmap_Tl: the supplied U transport intertwines Tl for every n, including
  the inadmissible case where Tl is zero.
- rpeigenAt_all: a bound at one splitting yields the bound at every
  splitting. rpeigen_of_one_splitting quantifies over every p prime,
  p%4=3, 3<p, and supplies exactly EDc4.RPEigen from the one-splitting
  hypothesis. The bound itself remains an explicit hypothesis.

Orientation was read against Section74a.psi. Both candidate identities
have C*psi_old=psi_new*C, hence psi_new=C*psi_old*C^-1, as used by Conj.
The determinant-sum proof supplies -4 and uses only 2≠0; no splitting
pair or residue class is silently excluded.

The EDc8 comments describing it as uncompiled are stale. This note records
the observed CI status without editing shared files or another lane's files.
No new Lean theorem was needed to meet the requested splitting scope.
No Lean compiler was invoked here; the previous private toolchain is absent.
No workflow was dispatched and no publication attempted.
RPEigen remains open. Geometric identifications belong to the other lanes.
