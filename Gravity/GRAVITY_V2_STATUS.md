# Gravity Across Scales v2: status as of 21 Nov 2026

Draft by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. Nothing here is released or uploaded.

## In this folder
- `AUDIT_GravityScales.md`, `audit_gravity_scales.py`: audit of the 18 Jun 2026 paper.
- `GRAVITY_LAW_READING.md`, `gravity_law_reading.py`: reading of Kepler, Newton and Schwarzschild as anchors of the dm³ chain.
- `GRAVITY_V2_PLAN.md`: decisions for v2.
- `GRAVITY_V2_DRAFT.md`: draft 1 of the v2 text.
- `moon_hill_roche.py`: recompute script for the Earth–Moon anchor (controls pass).

## Also in this folder (added 21 Nov 2026)
- `GravityAcrossScales_v1_with_corrections.html`: the v1 chapter (text unchanged) with amber correction boxes and blue added boxes; presentation version for students.
- `GRAVITY_V2_DRAFT.md` and `GravityAcrossScales_v2_draft1.html`: the paper version for Zenodo (template for how to write a paper); the HTML rendering is plain and is to be rebuilt as an annotated exemplar.
- `v2_math.py`, `v2_math.out`, `hill_stability.py`: scripts behind the numbers.
- The live chapter `chGravity-scales.html` in the geometry repo is not changed.

## Not done
1. PDF rebuild (the repo has no .tex; v2 must be typeset from the draft).
2. HTML pages: `law3m.html` and `chGravity-scales.html` (not yet read; need the cut header and the corrected claims).
3. Table 1 rewrite: the draft only says to add a measurement column and a strength label; the rows themselves are not revised.
4. Section 8 to 11 of the earlier paper, the references and the figures: not checked.
5. Done 21 Nov: Hill critical point is an index-1 Morse saddle, not an A1 fold; boundary r* is the stable manifold of the saddle (10-digit agreement); T1 proved on an invariant region (`v2_math.py`, `hill_stability.py`). Still open: the map between the ODE and Hill or Schwarzschild systems, and the z ↔ slow-variable reading (z is the accumulated twice-area, a monotone clock; the forcing 2(r−1)e^{−z} decays with it).
5b. Found while reading the HTML chapter `chGravity-scales.html`: its box "What would turn this conjecture into a theorem" lists a Lorentzian metric, a field equation and a recovery of Newton/Schwarzschild. That is the framing you rejected (the framework is a taxonomy that reads known laws); it needs rewriting. The chapter also gives r* = 0.77594058 while the PDF gives 0.77594059; the rounding of the certificate is ...058.
6. The 0.5 r_H prograde limit now matches a numerical scan (first escape at 0.50, T = 400); the retrograde limit is not tested (scan horizon too short).
7. Decisions for the author: final title, wording, whether the "17 orders" slogan stays on the hub pages, and the Zenodo upload.
