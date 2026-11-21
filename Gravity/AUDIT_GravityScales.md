# Audit note: "Gravity Across Scales" (Grossi 2026)

Status of this file: written 21 Nov 2026 as a working audit of `GravityScales_dm3_Grossi2026_Zenodo.pdf` (uploaded 18 Jun 2026). It is an internal audit by the author and an AI assistant (Claude, Sonnet 5.5), not an independent referee report. Independent checking is welcome; see "How to check this yourself".

## What this paper is
A study of a three-variable dynamical system on the contact manifold (R^3, dz - r^2 dθ), with a helix attractor, a basin boundary and a saddle, plus a set of conjectural identifications with string theory, QCD and galactic dynamics. Only the contact-geometry and dynamical-systems part is mathematics. The rest is labelled conjecture in the paper and stays conjecture.

## Results of the audit (script: `audit_gravity_scales.py`)

| Claim in paper | Result | Note |
|---|---|---|
| T3: saddle polynomial x^3 - x^2 - 2x + 1, discriminant 49, roots 2cos(kπ/7), k = 1, 3, 5 | PASS | exact algebra, rechecked in sympy |
| T3: saddle at r_s = 2cos(3π/7) ≈ 0.4450, z_s = -log(r_s(1+r_s)/2) | PASS | fixed point to machine precision |
| T3: tr J = 2cos(2π/7) ≈ 1.24698 | PASS | |
| T3: det J ≈ -0.3647 < 0, so a saddle | PASS | |
| T1: unit helix is invariant | PASS | by substitution |
| T1: all r0 > r*, z0 ≥ log 2 attract to the helix | PASS on a grid | 100 initial conditions, no failures. Not a proof. |
| T1: rate μ = -2 | Asymptotically correct | linearisation gives -2; the stated global bound |r-1| ≤ |r0-1|e^{-2t} is not proved (the proof uses "o(V)") |
| T2: r* = 0.77594059 | REPRODUCED, with a condition | obtained only with initial z(0) = 0 (r* = 0.775940576). |
| T2: r* is a constant of the geometry, valid for z0 ≥ log 2 | FAIL | the boundary depends on z(0): r*(0) = 0.7759, r*(log 2) = 0.5722, r*(1) = 0.4828, r*(2) = 0.2390, r*(3) = 0.0975. The paper's hypothesis z0 ≥ log 2 does not give 0.7759. |
| T2: r* is a Whitney A1 fold of the asymptotic map | NOT SUPPORTED | the asymptotic map is 1 on one side and undefined on the other, so "dΦ/dr0 = 0, d²Φ/dr0² ≠ 0" has no meaning. What is observed is a basin boundary, plausibly the stable manifold of the saddle. |
| T4: (R^3, α) is locally Sasakian | TRUE, proof wrong | the statement follows from the Darboux local model; the proof cites Gray stability as classifying contact structures on compact 3-manifolds, which is false (and R^3 is not compact) |
| Table 1, row g64 marked "Proved" | NOT SUPPORTED | rests on T2 |
| T-duality: T* = 2π is the self-dual radius | NOT SUPPORTED | T* is the period of θ; the self-dual radius depends on α' and units |
| Whitney A1 → A3 matched to SU(2) → SU(4) by McKay | NOT SUPPORTED | same letter "A", different objects (fold singularities of maps vs. orbifold singularities C^2/Z_n) |
| String field theory dictionary, g-series, Hill sphere, Milkomeda, Cajueiro cycle | CONJECTURE | labelled so in the paper; no derivation |
| "Gravity" | NOT PRESENT | there is no mass, no G and no recovery of Newton or Kepler from the equations; the title overstates the content |

## What the next version should say
1. Report r*(z0) as a curve; state that 0.77594059 is its value at z0 = 0.
2. Present T2 as a numerical observation about the basin boundary, not a Whitney fold, until a proof exists.
3. Replace the proof of T4, or cite Darboux.
4. Remove "Proved" from the g64 row.
5. State once, in the introduction, that string theory is used as the target framework, that the identifications are proposals, and that the proved content is the contact-geometry and dynamics part.
6. Either derive a gravitational law from the system or retitle the paper.

## How to check this yourself
`python3 audit_gravity_scales.py` (needs numpy, scipy, sympy). It prints PASS/FAIL per check and the basin boundary for several z(0). The bisection tolerances are in the script. If you find an error in the audit, please open an issue.

## What was not checked
The references, the figures, and Sections 8 to 11 beyond reading them. No independent referee has read this paper.
