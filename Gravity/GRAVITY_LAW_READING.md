# Reading a gravitational law through the dm³ contact system

Written 21 Nov 2026 by Claude (Sonnet 5.5) with Pablo Nogueira Grossi. Companion to `AUDIT_GravityScales.md`. Script: `gravity_law_reading.py` (sympy; every line below marked "checked" is printed by it). This is a reading of known physics in the paper's language. It is not a derivation of any gravitational law from the dm³ system, and it does not claim one.

## The translator
The contact manifold is (R³, α = dz − r² dθ). Take a planar motion about a centre with angular momentum per mass h = r²θ̇. Let z be twice the swept area, so ż = h. Then dz = r² dθ along the motion, that is, α vanishes on the lifted curve.

## Three laws, three readings

**1. Kepler's second law is the contact condition. Checked, exact.** Equal areas in equal times is ż = h = constant. A motion under any central force lifts to a curve with α = 0 (a Legendrian curve). So the paper's contact condition "vertical lift equals angular momentum" is the areal law. It holds for every central force, not only gravity, so it carries no information about gravity itself.

**2. Newton's circular-orbit law has no fold. Checked.** For Newtonian gravity L²(r) = GM·r, so dL²/dr = GM never vanishes. There is no innermost stable radius and nothing like a lock gap. This part of the paper's introduction is right for Newton.

**3. Schwarzschild circular orbits have a genuine Whitney A1 fold. Checked, exact.** L²(r) = M r²/(r − 3M) in units G = c = 1. Its derivative vanishes at r = 6M, the second derivative there is 2/3 ≠ 0, and the effective-potential second derivative changes sign across 6M (negative at 5M, zero at 6M, positive at 7M). So the map from radius to angular momentum of circular orbits has a non-degenerate fold at the innermost stable circular orbit (ISCO), with L² = 12M² there. This is a true fold of a map, the object the paper wants to call "the lock gap". It sits in general relativity (Einstein, 1915, through Schwarzschild), not in Newton.

**Consequence for the paper.** The introduction says that Brahmagupta, Newton and Einstein "none explained the lock gap". That is wrong for Einstein: GR gives a stable-orbit boundary at 6GM/c², and above it quasi-circular orbits are stable while below it they plunge. v2 should say that Newtonian gravity has no such radius and that GR has the ISCO, and should present the dm³ system as a toy with the same qualitative structure (stable region above a boundary, collapse below), not as the explanation of something GR leaves open.

## Where the translation fails (checked)
- **Conservative versus dissipative.** Newtonian orbits conserve energy; the radial epicyclic frequency equals the orbital frequency (ratio 1), so orbits are closed and neutral. They have no attractors. The dm³ helix is an attractor with radial rate −2, an overdamped system. Reading it as gravity needs a dissipative mechanism (accretion-disc viscosity, tidal friction, drag) that the paper does not supply. In an accretion disc, matter loses angular momentum slowly through stable circular orbits and plunges at the ISCO, which is the closest physical match to "outer basin attracts, inner basin collapses".
- **The numbers do not match.** The Schwarzschild radii give ratios ISCO/photon sphere = 2 and ISCO/horizon = 3. The dm³ constants give r_s/r\* = 0.5736. No ratio from one set equals any from the other, and no map between the systems has been written down, so the resemblance is qualitative only.
- **Scale.** In the paper's units the helix sits at r = 1 and absorbs G, M and h into the choice of units. The system contains no gravitational constant, so no inverse-square or other law can be read off from it.

## What would turn this into a result
1. Write the dm³ radial equation as an overdamped motion in a potential, ṙ = −∂V/∂r with V = r⁴/4 − r²/2 (the e^{−z} term aside), and state which gravitational effective potential it approximates.
2. Specify the dissipation that makes the Schwarzschild or Newtonian circular orbits an attractor, then compare the resulting basin boundary with the ISCO.
3. Only then compare constants. Until step 1 and 2 are written, the claim is a shared shape, not a shared law.

## Literature already in the repo that bears on this
`MUELLER_REVIEW_MAP.md` §3 (the same L²(R) formula and the same 6M minimum), `FERREIRA_REVIEW_MAP.md` and its Hawking–Ellis rows (conjugate points and folds, the Schwarzschild stable radius), and `book7/ch-schwarzschild-verify.py` in the geometry repository. This note's reading of the ISCO fold agrees with those and goes one step further by stating the second-derivative check.

## Addendum: what the two PDFs in Downloads add (read 21 Nov 2026)
Read: Ferreira, review of modified gravity (arXiv 1902.10503v3), the passages on Lovelock's theorem (intro), the relativistic Newton–Poisson equation (eq. 5) and the screened-scalar effective potential (eq. 28); Hawking & Ellis (1973), the passages on geodesic motion of small bodies, the Newtonian limit that fixes the field equations, and the table of contents for §5.5. Not read: the rest of both. Hawking–Ellis, as extracted here, contains no ISCO or circular-orbit stability computation, so the 6M result above rests on the sympy check, not on that book.

**Correction to my first draft of this addendum (author's instruction, 21 Nov 2026).** I had framed the task as deriving a law from the dm³ system, so that it would need G, a mass and a field equation. That is the wrong job. The framework is a translator: it takes phenomena and laws that are already known and reads them in the operator language G = U∘F∘K∘C (compression, curvature, fold, unfolding). It does not propose a new law. The absence of G in the ODE is therefore not a defect, and the field being read is the 3-manifold itself; G, M and the field equation belong to the known law being read, and the bridge is the dictionary between the two. The audit row "no gravity present" stands only for the paper's title, which promises more than a dictionary.

**What the sources supply: the known laws to be read.** Ferreira (citing Lovelock 1972): Einstein's equations are the only second-order local field equations from a 4D metric action. Hawking–Ellis: field equations fixed by the Newtonian limit; small bodies follow timelike geodesics. Ferreira eq. 5: Newton–Poisson, −k²Φ = 4πGΔρ. These are the inputs. The deliverable is a translation table.

**Role of the framework (author's statement, 21 Nov 2026).** The dm³ chain and the g-series are taxonomies. They give every kind of phenomenon a place and an anchor, so that what is understood about a phenomenon in one domain or at one scale can be carried to another. Under that reading an entry in the table below is an anchor, not a derivation or an identity claim. An anchor is acceptable when both sides are written down: the known structure (a law, a threshold, a fold, a measured quantity) and the operator slot it occupies. Entries then differ in strength. Strong: the anchor on the known side is a checked structure (Schwarzschild ISCO fold, Kepler's second law as α = 0). Weak: the slot is proposed and the known-side structure is not yet identified as the same type (Hill sphere, Poisson). The scale ladder in Table 1 of the paper is then a list of anchors per rung, and a rung without a written-down known structure is an empty slot, not a failed prediction.

**Translation table (dictionary proposals; the algebra in column 3 is checked, the operator labels are the author's reading and are not derived).**

| Known phenomenon | Operator reading | What is checked |
|---|---|---|
| Newton–Poisson ∇²Φ = 4πGρ | The field is the 3-manifold: the dm³ counterpart of the potential is the contact structure on M = (R³, α) itself, with α the potential 1-form and dα its field strength. K: the Poisson law says the curvature of the potential equals its source | in Cartesian form α = dz − (x dy − y dx), so dα = −2 dx∧dy is constant and α∧dα = −2 dz∧dx∧dy ≠ 0 (contact), sympy. The identification with Φ is a reading; no source term is written down |
| Newtonian circular orbits L² = GMr | C and K with no F: L² is monotone, no fold, chain does not close | dL²/dr = GM ≠ 0 |
| Schwarzschild circular orbits | K: V_eff'' falls toward 0 as r decreases to 6M. F: A1 fold of L²(r) at 6M. U: stable circular orbits above, plunge below | V_eff'' sign change across 6M and d²L²/dr² = 2/3 at 6M (sympy) |
| Hill sphere (restricted three-body, Hill's approximation) | the saddle slot, not the fold: the L1/L2 critical point of W = 3x²/2 + 1/r is an index-1 Morse saddle, like the dm³ boundary saddle whose stable manifold is the basin boundary | Hessian diag(9, −3), det −27 (sympy). The wording "A1 fold" for the Hill sphere is not supported (21 Nov 2026 update) |
| Kepler's second law | the contact condition α = 0, exactly | see section 1 above |

**Step 1, checked.** ṙ = r(1−r²) equals −dV/dr for V = r⁴/4 − r²/2 (sympy). V has a maximum at r = 0 and a minimum at r = 1 (V = −1/4). This is a double-well-type potential; it is not a gravitational effective potential. The Schwarzschild one is V_eff = ½(1−2M/r)(1+L²/r²), whose extremum condition reproduces L² = Mr²/(r−3M) (sympy: derivative vanishes identically on that curve). Their shapes differ: V_eff has a maximum and minimum that merge at r = 6M as L² falls to 12M², V above has fixed wells. The basin boundary at r ≈ 0.78 exists only through the dropped e^{−z} term, so step 1 alone does not give an ISCO analogue.

**Ferreira eq. 28 as the one real bridge.** There the scalar field obeys φ̈ + dV_eff/dφ = 0 with V_eff depending on local density, giving a mass m² = d²V_eff/dφ². That is the structure "stability = sign of a second derivative of an effective potential", the same criterion that places the ISCO. It is a modified-gravity model, not a dm³ result, and I am noting it only as the literature's template for step 2, where a density- or z-dependent term plays the role of e^{−z}.

**Conclusion.** Read as a taxonomy with anchors, the dm³ chain already matches the Schwarzschild ISCO structure (K, F and U all present) and shows Newton as the case where the chain does not close; the Hill sphere is a plausible further entry that still needs the fold type checked. The three steps above are reframed accordingly: step 1 means stating which known effective potential each dm³ term translates, step 2 means stating which known dissipative mechanism makes the translated orbits attractors, and step 3 means comparing constants only inside an entry where both sides are written down. Suggested v2 title: replace "Gravity" with the translation claim, for example "A taxonomy of gravitational phenomena anchored in the dm³ chain".
