# Referee ledger: Mueller, "The Lorentz Factor as the Slope of an Additional Spatial Coordinate: Embedding, Painlevé–Gullstrand Flow, and the Issue Of Simultaneity"

Zenodo preprint, v1, 16 November 2026 (A. Mueller, independent researcher). Prepared 20 Nov 2026 (G6 LLC). Working ledger, unreviewed by a specialist or a second system. The author has not seen it. Nothing in this folder has been sent to the author or to anyone.

## Scope: what was read and what was not

Read in full or in the part that carries claims: abstract; §2.2.1–2.2.2 (Lorentz factor as a slope); §2.3.2–2.3.5 (G44, Cassini, vacuum equation for G44); §2.4.3–2.4.6 (induced geometry, curvature, temporal closure); §2.5 and §2.5.1 (Proposition 1, interior solution, Buchdahl); §2.6–2.8.4 (orbits as summarised, higher-dimensional metric, Painlevé–Gullstrand, Hubble flow); §3 (Hypothesis M and the Milky Way comparison); §4.6–4.7; Appendix A introduction, A.4, A.5, Table A3.

Not read: §1 and §1.1 (introduction and the lighthouse text, beyond the blog version), §2.1 (dictionary) and Table 1; §2.3.6 (matter-sourced equation for the fifth-dimensional metric) and §2.4.1–2.4.2 (off-diagonal terms); §4.1–4.5; Appendix A.1–A.3 and A.6 (fine-structure and electromagnetic alignments); the derivations in Appendix B (only the results quoted in §2.6 were checked); the reference list. The rotation-curve data (Eilers et al.) and the baryonic profiles (Cautun et al., McMillan) were not available, so no χ² was recomputed.

The author's own scope statements are taken as stated: the Hamiltonian constraint and the static vacuum equations are imported from general relativity (§2.4.4, §2.5, §2.8.4); the construction is "equivalent to general relativity" only in vacuum or pressureless matter with spherical symmetry; Hypothesis M is an assumption with a one-galaxy comparison that "does not determine κ′".

## Files

- `MuellerChecks.lean`: Lean 4 + Mathlib, 24 theorems, no `sorry`, axiom reports for the nine headline theorems show only propext, Classical.choice, Quot.sound.
- `check_sympy.py`: symbolic checks that need second derivatives of square roots (ALL PASS).
- `check_numbers.py`: quoted numbers recomputed from public constants, with controls (ALL PASS).

## Results table

| Item | Paper | Status | Where |
|---|---|---|---|
| γ = √(1+(∂ₓy)²), ∂ₓy = βγ | (22)–(27) | checked, exact | Lean `gamma_eq`, `sx_sq`; sympy spot checks |
| ∂ₓy = sinh of rapidity, γ = cosh | not stated | checked (this ledger's observation) | Lean `slope_is_sinh` |
| Lighthouse bookkeeping: (d/γ)/v = (d/v)/γ | §1.1 (blog) | checked | Lean `lighthouse` |
| (3)R = 4ββ′/R + 2β²/R² = (2/R²) d(Rβ²)/dR | (109), (118) | checked | Lean `scalar_curv_form`, `deriv_R_beta_sq` |
| β² = 2Gm/(c²R) from (3)R = 16πGρ/c² | (110) | checked given the constraint | Lean `beta_sq_mass` (assumes differentiable on ℝ, regular centre) |
| Exterior y = 2√(rₛ(R−rₛ)), slope βγ | §2.4.4 | checked | Lean `exterior_slope`, `exterior_beta_gamma` |
| Cap y = √(L²−R²), slope βγ, β = R/L | §2.4.4 | checked | Lean `cap_slope`, `cap_beta_gamma` |
| Slice curvature 0 (exterior), 6/L² (cap) | §2.4.4 | checked | sympy |
| Critical density: L = c/H, rₛ(c/H) = c/H | §2.4.4 | checked | Lean `critical_L`, `critical_rs` |
| N = √(1−rₛ/R) solves the angular ODE | Prop. 1 (119)–(121) | checked | Lean `lapse_log_deriv`, `prop1_ode`, `prop1_rhs` |
| N,ℓℓ/N = 2ββ′/R (radial component) | Prop. 1 | checked | sympy |
| g₀₀ h_RR = −1 | after Prop. 1 | checked | Lean `g00_hRR` |
| Interior (125) satisfies TOV gradient and hydrostatic equilibrium | §2.5.1 | checked | sympy |
| Buchdahl: 3s*>1 ⇔ R*>9rₛ/8; p_c/ρ = (1−s*)/(3s*−1) | §2.5.1 | checked | Lean `buchdahl_iff`; sympy |
| PG metric: h_RR = γ²; change of time to Schwarzschild form | (133)–(135) | checked | Lean `pg_hRR`, `pg_to_schwarzschild` |
| Hubble flow β_H² = 2Gm/(c²R) | (136) | checked | Lean `hubble_beta` |
| Φ = Φ∞(1+q ln(1−rₛ/R)) solves (52) | §2.3.5 | checked | sympy |
| v_local² = GM/(R−rₛ), L² = GMR²/(R−3GM/c²) | §2.6 | checked | sympy |
| Perihelion advance 42.98″/century (Mercury) | (129) | checked, control agrees with observation | numbers |
| Cassini: ω_BD ≳ 4×10⁴ | (51) | checked | numbers |
| §3.1 ratios 10⁻⁵ and 3×10⁻⁴; H₀R = 0.6–1.8 km/s | §3.1 | checked | numbers |
| Sciama identity G m_H/(c²R_H) = 1/2 | (137) | checked; follows from the definition of critical density | numbers, Lean |
| g₀ = cH₀/2π = 1.1×10⁻¹⁰ m/s²; Table A3 ratios; v_orbit = 216.9 km/s | §3.5, A33 | checked | numbers |
| Earth "kinematic velocity" | A31 | recomputed with one choice of radius and mass; differs slightly from the quoted value; under reconciliation, not asserted | numbers |
| Sun, Saturn, Moon ≈ 190, 130, 290 km/s; v_cosmo/v_kin = √2 | Appendix A | recomputed, agree | numbers |

## Ledger by status

**A. Algebra and calculus checked (Lean or sympy).** Every row marked "checked" above. Every one is true as stated.

**B. Imported from the literature, not checked here.** Gauss equation and the form of the extrinsic curvature of a hypersurface in flat ℝ⁴; Schwarzschild, Painlevé–Gullstrand, FLRW, TOV and Buchdahl results as quoted from the literature; the Cassini measurement; Milgrom's modified-inertia framework; the interpolation function of [39]; the baryonic Tully–Fisher relation; Eilers et al. rotation-curve data.

**C. Checkable in principle but beyond current Mathlib.** Statements about the Levi-Civita connection, Riemann and Ricci tensors, the Einstein equations, the Gauss–Codazzi equations for an embedded hypersurface, geodesics on a pseudo-Riemannian manifold, and "equivalent to general relativity" as a theorem. Checked 20 Nov 2026 by searching the Mathlib source at the revision used for the Lean files here (commit 81a5d257, 13 July 2026): it has smooth manifolds, Riemannian manifolds (`IsRiemannianManifold`, path length), covariant derivatives on vector bundles, torsion of an affine connection, and metric-compatible connections. A text search found no definition of the Levi-Civita connection and none of Riemann or Ricci curvature, and nothing for Gauss–Codazzi or pseudo-Riemannian signature. Separate projects outside Mathlib do have Levi-Civita and Ricci curvature in Lean (see the how-to guide's further reading), so "beyond Mathlib" does not mean "not done anywhere". The coordinate-level steps above are the part that can be done today. A hand-built coordinate treatment of the Schwarzschild metric (Christoffel symbols, Ricci = 0) is possible but is not done here.

**D. Assumptions or closures stated by the paper.** The Hamiltonian constraint (3)R = 16πGρ/c²; the static vacuum equations (114); the temporal closure N = 1/γ (derived in vacuum from the imported equations, a closure elsewhere); five-dimensional vacuum for G44 (§2.3.5); the definition of y by ∂_R y = βγ; Hypothesis M, the interpolation function and κ′.

**E. Not claimed by the paper.** A derivation of general relativity from the fourth coordinate; that Hypothesis M explains Galactic rotation; any role for the fine-structure constant (Appendix A.6); the physical identification of the characteristic velocities with the CMB dipole or supernova flows; Buchdahl's theorem beyond uniform density; non-gradient potential and field equations for G44 (§4.6).

## Findings

Held back. Draft observations about the paper are not published here: they are unreviewed, one numerical point is still being reconciled with an earlier pass, and the author has not been contacted.

## What remains for a specialist

- Whether the five-dimensional embedding with a non-compact flat fourth coordinate has a covariant action (§4.6 says it does not yet) and what field equations G44 and the non-gradient potential obey.
- Hypothesis M: relativistic completion and cluster-scale behaviour of modified-inertia theories (the paper notes these difficulties); a sample of galaxies with measured baryonic masses.
- The Appendix A alignments (fine-structure constant, characteristic velocities) are numerical observations; whether any survive a pre-registered test is for the author.
- The sections not read (listed above), in particular §2.3.6 and Appendix B.

## Limits

Everything here is a check of internal consistency and of quoted numbers. A passing check shows that a step follows or that a number can be recomputed from public constants, not that the physics is right. No data were available for the rotation-curve fits.
