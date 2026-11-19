# Claims ledger and referee brief — internal working draft

**Paper:** A. Mueller, "The Lorentz Factor as the Slope of an Additional Spatial Coordinate: Embedding, Painlevé–Gullstrand Flow, and the Issue of Simultaneity", Zenodo 10.5281/zenodo.24280888 (16 Nov 2026), 62 pp.
**Prepared:** 19 Nov 2026, for G6 LLC internal use. **Nothing here has been sent to the author or anyone else.**
**Scope of what was read:** main text §1–§4 and Appendix A in full; Appendix B (standard Schwarzschild orbit derivations, B.1–B.4) and the reference list were **not** reviewed line by line.

## 1. What the three scripts establish

| File | What it checks | Result |
|---|---|---|
| `MuellerCore.lean` | 11 theorems (Lean 4.32.0, Mathlib 81a5d257): eqs 14/26 (γ² = 1+(∂ₓy)²), slope = γv/c, 18–21 (interval invariance at dt = 0), 49/134 (1+β²γ² = γ²), 144–146 (Flamm slope), 88–89 (Φ′ = Q/(R(R−rs))), 121 (N′/N for N = √(1−rs/R)), 126 (3√(1−rs/R) > 1 ⇔ R > 9rs/8), 137 (Sciama identity, r_s(c/H) = c/H), 68→72 (scalar source), 140 | compiled, rc 0, every theorem depends only on propext, Classical.choice, Quot.sound |
| `check_sympy.py` | 29 symbolic re-derivations including eqs 63–68, 109/118, 120–125 (interior Schwarzschild, hydrostatic equilibrium, TOV gradient), 96, 129-adjacent orbit speed | all pass (2 by exact-rational spot checks where sympy cannot simplify a root) |
| `check_numbers.py` | 21 recomputations of Appendix A and §3 figures from public constants | all pass; see §3 for what that does and does not mean |

These establish that the **displayed algebra follows from its stated premises**. They do not establish any physical claim.

## 2. Ledger, by status

**A. Algebra, machine-checked (Lean and/or sympy):** eqs 11–16, 17–21, 26–27, 44, 48–49, 88–89, 91–97, 109, 117–121 (Prop. 1's ODE step and the radial component), 122, 124–126, 134, 137, 140; the Flamm and uniform-density embeddings of §2.4.4; the critical-density statements (r_s(c/H) = c/H).

**B. Imported from general relativity, not derived by the paper (the paper says so):** the time-symmetric Hamiltonian constraint ³R = 16πGρ/c² (so β² = 2Gm/(c²R)); the static vacuum equations ³Rᵢⱼ = ∇ᵢ∇ⱼN/N, ΔN = 0; the Painlevé–Gullstrand form (eq 133); the Friedmann equation; the Schwarzschild orbit results of §2.6 / Appendix B; the 5D vacuum condition R_yy = 0 and the 5D reduction (eqs 53–63, standard warped-product formulas).

**C. Checkable on paper but beyond current Mathlib (the paper's own scope note applies):** the Gauss equation for a hypersurface of flat R⁴ (eq 108, 115); the principal-curvature argument of eqs 116–118 (hand-verified here: the sectional curvatures κ_Rκ_θ = ββ′/R, κ_θκ_φ = β²/R² and the trace identity reproduce eq 109); the statement that the Schwarzschild slice embeds in flat R⁴ as a hypersurface of revolution; the Campbell–Magaard citation.

**D. Assumptions or closures, labelled as such by the paper:** G₄₄ = 1 normalisation (checked only against the Cassini bound γ_PPN − 1 = (2.1 ± 2.3)×10⁻⁵, and the equivalence is a definition of y, not a derivation); regularity at r_s forcing q = 0 (eq 52); the closure N = 1/γ (§2.4.5, then "derived" for static vacuum in §2.5 — see §4 below); Hypothesis M (μ-function, cutoff at c²/g, g₀ ∝ cH₀, κ′); the "classical simultaneity" assertions of §1.1 (eqs 3–5), which §4.1 itself says are not established.

**E. Not claimed as derived by the paper, correctly:** non-gradient potential aμ and its link to spin or electromagnetism; Buchdahl for non-uniform density; interior/time-dependent lapse beyond the uniform-density case.

## 3. Findings for the author (draft; none sent)

1. **v_cosmo/v_kinematic = √2 (eq A32) is an algebraic consequence of the definitions, not an observation.** v_cosmo uses φ−1 = GM/R³ and v_kin uses (φ−1)/2; for any small φ−1 the ratio is √2. `check_numbers.py` includes a control that fails to distinguish d = 10⁻⁹ from d = 10⁻⁴. The text already notes the √2 as "the ratio of escape to circular speed"; it should say it cannot be evidence.
2. **A23 as printed is dimensionally inconsistent** (GM + 2R³ adds m³ s⁻² to m³) and is valid only after setting τ̂ = 1 s, which the appendix's dimensional note admits. The result is numerically √(2GM/R) to within ~10⁻³¹, so A23 adds nothing beyond the escape speed. The paper says this; the displayed formula should carry the factor.
3. **Appendix A numerology is acknowledged as post hoc.** ω⊕ = α(2−α) was chosen after 2α was found to be 0.39% off (recomputed: 2α off by 0.39%, α(2−α) by 0.025%). With ~one free choice per body, 0.5% agreement is expected by chance; the paper says so. Recommend moving to a clearly separated "unexplained coincidences" note, or dropping from the abstract's claims.
4. **The 371,580 m/s vs Planck dipole (369.82 km/s) agreement is 0.48% and the paper concedes the difference exceeds the measurement uncertainty.** Recomputed 0.48%.
5. **§2.5.1: "tilt below 70.5°"**: arccos(1/3) = 70.53°; trivial, but the stated bound is slightly too tight.
6. **Prop. 1 (derived lapse):** the ODE step is correct (Lean-checked). The logical status is an equivalence: given the imported static vacuum equations, N is fixed by the slope. The paper states this (§2.5 "What is and is not established"). The abstract's "not postulated: it follows from the Gauss equation of the embedding together with the static vacuum field equations" is accurate only with that qualifier retained.
7. **§3.5 fit to one galaxy:** Table A3's g₀/(cH₀) = 0.35, 0.22, 0.15 recomputes from g₀ = 2.4, 1.5, 1.0×10⁻¹⁰ m s⁻². The χ²/dof are not recomputable without the authors' baryonic model ("typed from memory" per the text); not checked.
8. **§2.8.2 and the Hubble-flow sign:** correct as stated and standard (flat FLRW in areal coordinates).

## 4. What remains for a specialist

Gauss–Codazzi for the embedding, the PG/LTB literature claims (§2.8.3), the Misner–Sharp mass statement, the relation of Hypothesis M to Milgrom-type modified inertia and to the cited criticisms, the interpretation of Appendix A's physical content, and Appendix B. A Lean formalisation of the hypersurface curvature steps would need a semi-Riemannian layer that Mathlib does not yet have (the outreach draft's own scope note says the same).

## 5. Limits of this brief

Prepared by Claude (Anthropic) for Pablo Grossi / G6 LLC. It checks the paper's arithmetic and one-variable calculus; it is not a physics review and not an endorsement or refutation. All sources are the paper's PDF as uploaded and public constants. No outreach has been sent.
