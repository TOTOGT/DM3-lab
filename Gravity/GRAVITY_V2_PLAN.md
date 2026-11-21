# Plan for "Gravity Across Scales" v2

Written 21 Nov 2026 by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. A plan, not the paper. Decisions below come from this session's conversation and from `AUDIT_GravityScales.md` and `GRAVITY_LAW_READING.md`.

## Role of the paper
The dm³ chain and the g-series are taxonomies with anchors. They let understanding of a phenomenon in one domain or scale carry to another. The paper does not propose a new law; it reads known gravitational phenomena in the operator language G = U∘F∘K∘C. The tilde on dm³ marks that the objects are dynamical (moving thresholds), to be stated once in the notation section.

## Front matter
1. Cut header: "Cut: contact-geometric; axis: length, 10⁻³⁵ m to 10²² m; builds on the symplectic paper." Any figure like "57 orders" is given with this cut and its arithmetic. The "17 orders" slogan (Coherence Bridge, hub and series pages) is not used here unless its rungs and derivation are shown.
2. Retitle: drop "Gravity" as a claim, for example "A taxonomy of gravitational phenomena anchored in the dm³ chain". Title decision is the author's.
3. One sentence on the tilde; one sentence that string theory is the target framework and the identifications are proposals.

## Mathematics (audit corrections)
4. Report the basin boundary as a curve r*(z0): 0.7759 (z0 = 0), 0.5722 (log 2), 0.4828 (1), 0.2390 (2), 0.0975 (3). State that 0.77594059 is the value at z0 = 0 only. The moving boundary is the object, as for the Moon.
5. T2 becomes a numerical observation about the basin boundary (plausibly the stable manifold of the saddle), not a proved Whitney fold.
6. T4: cite the Darboux local model; remove the Gray-stability argument (it is false for non-compact R³).
7. Remove "Proved" from the g64 row of Table 1.
8. Remove the T-duality self-dual radius claim and the A1→A3 / McKay match, or mark both as conjecture with the reason.
9. T1 rate: keep μ = −2 as asymptotic; drop the global bound unless a proof is supplied.

## Physics (anchors)
10. Correct the introduction: Einstein's theory does give a stable-orbit boundary (ISCO, 6GM/c²); Newton does not. Say so.
11. Anchor table, each row marked strong, proposed or empty: Kepler II = contact condition α = 0 (strong); Newton, no fold (strong); Schwarzschild ISCO fold with discriminant L²(L² − 12M²) and the unfolding r± (strong); Hill sphere (proposed; critical points located, fold type not shown); Poisson read as curvature of the field (proposed). The field is the 3-manifold (R³, α), with dα = −2 dx∧dy.
12. Worked anchor with real dynamics: the Earth–Moon tidal recession against the Hill threshold (about 0.5 r_H for stable prograde orbits) and the Roche limit, with a script that recomputes the numbers from G, masses and a.
13. Table 1 gets a column: what is measured at each rung, and a strength label. Empty rungs are empty slots, not failed predictions.
14. Universality hypothesis stated once, with its falsifier: a rung with a known threshold that the chain cannot place. State the scale-free fact (α → λ²α under r → λr, z → λ²z) separately from the physical claim.

## Checks to run before release
- `audit_gravity_scales.py` and `gravity_law_reading.py` pass; add the Moon/Hill/Roche script.
- Every number in the paper traces to a script or a cited source; machine-condensed claims are listed as unverified until traced.
- Say what was not checked (references, figures, Sections 8–11 beyond reading, as in the audit note).

## Deliverables
Paper v2 PDF (rebuilt: the repo has no .tex), updated HTML pages (law3m.html, chGravity-scales.html), a new Zenodo version (uploaded by the author), and the audit note linked from the repo README.
