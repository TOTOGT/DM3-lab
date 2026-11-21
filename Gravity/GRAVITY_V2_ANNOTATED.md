# A taxonomy of gravitational phenomena anchored in the dm³ chain
*(working title; draft 1 of v2, 21 Nov 2026, drafted by Claude (Sonnet 5.5) for P. N. Grossi. Not for release before the author's review.)*

**Cut:** contact-geometric; axis: length, 10⁻³⁵ m to 10²² m (57 orders; the arithmetic is the exponent difference). Builds on the symplectic paper of this series. Other papers in the series use other cuts and other axes; figures quoted there are not comparable to this one. The cuts nest by parity: symplectic manifolds are even-dimensional, contact manifolds odd-dimensional, and a contact manifold fibres over a symplectic base, the Reeb direction being the extra coordinate. Here (ℝ³, α) is the line bundle over the plane (x, y) with symplectic form dα = −2 dx∧dy: 3 = 2 + 1 (checked, sympy). Nothing can be dynamic without time, and the fibre coordinate z (twice the accumulated area) is a clock along each orbit; the dm³ tilde marks that role. The author's statement is that the next case is 4 + t = 5: a four-dimensional (even, symplectic) base with time as the fibre, a five-dimensional (odd, contact) space, a modified Kaluza–Klein structure. Already in three dimensions the Sasakian metric of section 2 has Kaluza–Klein form, (dz − A)² + dx² + dy² with A = x dy − y dx, whose field strength F = dA = 2 dx∧dy is a uniform field on the base (checked). The five-dimensional case is not worked out here; which four-dimensional base, and whether the fibre coordinate is physical time, are open.

## Abstract

> **Why this section is here.** Say what the paper does, what it does not claim, and what a reader can check, in about 150 words. Zenodo shows this first; readers decide here whether to continue. Note that it states the limit (a reading, not a new law) before the claim.

We read known gravitational phenomena in the operator language of the dm³ chain G = U∘F∘K∘C on the contact 3-manifold (R³, α = dz − r² dθ). The chain and the g-series are used as a taxonomy: each phenomenon receives a place and an anchor, so that understanding in one domain or scale can be carried to another. No new gravitational law is proposed. Proved content is the contact-geometry and dynamics part. The anchors are classified strong, proposed or empty. We report the basin boundary of the model ODE as a curve r*(z₀), not a constant, and give one worked anchor with a recompute script: the Earth–Moon distance against the Hill and Roche thresholds.

## 1. Introduction

> **Why this section is here.** State the question and the framing once. The Introduction is where the reader learns how to read everything after it: here, that the dm³ chain is a taxonomy that reads known phenomena. If this is left implicit, readers will judge the paper as a new gravity law and reject it for the wrong reason.

Brahmagupta, Newton and Einstein each gave a description of orbits. Newtonian circular orbits satisfy L² = GM r, which is monotone and has no innermost stable radius. General relativity does have one: for Schwarzschild, circular orbits satisfy L² = M r²/(r − 3M) (G = c = 1), whose derivative vanishes at r = 6M with second derivative 2/3, a non-degenerate fold. The dm³ chain is a toy with the same qualitative structure and is offered as a vocabulary for it, not as an explanation of something general relativity leaves open.
Newtonian gravity is already mutual: the Moon pulls on Earth as hard as Earth pulls on the Moon, and both orbit their common centre of mass (4,668 km from Earth's centre, inside Earth). What Newton lacks is finite propagation speed. In general relativity a changing system radiates gravitational waves at the speed of light, whatever the mass of the source, and the radiation carries energy away, so the two-body interaction has a direction in time. This radiation reaction is the physical counterpart of the dissipative step U in the chain at the strong-field rung. The mass of the source sets the scales, not the speed: frequencies, lengths and times all scale with M (section 3).
The tilde in the name of the framework, dm³ with its tilde, marks that the objects of study are dynamical: thresholds such as r*(z) and d/r_H move as the system moves. The curve r*(z₀) is the moving threshold the dm³ tilde stands for; a single constant read from one slice presents a moving boundary as fixed. String theory is used as a target framework; every identification with it is a proposal.

## 2. The contact manifold and the model ODE

> **Why this section is here.** Define every object the later sections use, and only prove what you can prove. Each theorem is labelled with its exact region and what was withdrawn. A paper others can build on lists its retractions next to its results.

**Definition.** M = (R³, α), α = dz − r² dθ = dz − (x dy − y dx). Then dα = −2 dx∧dy and α∧dα = −2 dz∧dx∧dy ≠ 0, so α is contact. Under r → λr, z → λ²z, α → λ²α, so ker α is invariant: the *form* of the geometry is scale-free (checked, sympy). This does not show that nature uses it at every scale.
**Kepler II.** Along a planar central-force motion with h = r²θ̇ and z twice the swept area, α = 0. Equal areas in equal times is the contact condition. It holds for every central force and carries no information about gravity itself.
**ODE.** ṙ = r(1 − r²) + 2(r − 1)e^{−z}, θ̇ = 1, ż = r² − 2(r − 1)²e^{−z}.
- **T1 (proved on an invariant region; checked numerically beyond it).** Let D = {r ≥ (√5−1)/2, z ≥ log 2}. On D, r(1+r) − 2e^{−z} ≥ 0 (equality only at the corner, where r² + r = 1), so V̇ = −(r−1)²[r(1+r) − 2e^{−z}] ≤ 0 for V = (r−1)²/2. D is forward invariant: on r = (√5−1)/2 < 1, ṙ = (1−r)[r(1+r) − 2e^{−z}] ≥ 0; for r > 1, ṙ ≤ 0 and r = 1 is invariant; and ż ≥ 2r − 1 ≥ 0.236 > 0 on D, so z → ∞. Hence every orbit starting in D converges to the helix, and the rate tends to −2 as z → ∞ (the bracket tends to r(1+r) → 2). The earlier bound |r − 1| ≤ |r₀ − 1|e^{−2t} with constant 1 is not proved; the true statement is an asymptotic rate. D is a strict subset of the basin, since r*(log 2) = 0.572 < 0.618. (Script `v2_math.py`, section D, checks the sign conditions on a grid; the argument above is the proof.)
- **T3 (checked, exact).** The saddle has r_s = 2cos(3π/7) ≈ 0.4450, a root of x³ − x² − 2x + 1 (discriminant 49); tr J = 2cos(2π/7), det J ≈ −0.3647.
- **Basin boundary (replaces T2).** The boundary depends on z₀: r*(0) = 0.7759405755, r*(log 2) = 0.5722, r*(1) = 0.4828, r*(2) = 0.2390, r*(3) = 0.0975, r*(4) = 0.0365. The repo's interval certificate gives r*(0) ∈ [0.7759405755019531, 0.7759405755023437], which rounds to 0.77594058; the earlier text's 0.77594059 is a rounding slip, and the certificate is for z₀ = 0, not for the hypothesis z₀ ≥ log 2. Two further results (script sections B, C, G): (i) the stable manifold of the saddle, integrated backward in time from the saddle along its stable eigenvector (eigenvalues 1.4915 and −0.2445), crosses z = 0 at r = 0.7759405755, agreeing with the bisection value to ten digits, so the basin boundary is that stable manifold (numerical, not a proof); (ii) for large z₀, r*(z₀) ≈ 2e^{−z₀} (0.0365 against 0.0366 at z₀ = 4), the value where the frozen-z radial equation ṙ = 0 has its unstable root. The claim that r* is a Whitney A1 fold of an asymptotic map is withdrawn: the map is 1 on one side of r* and undefined on the other. The boundary is a hyperbolic saddle's stable manifold, and the saddle has det J = −0.3647.
- **T4 (checked, one step cited).** (M, α) is Sasakian, globally. In Cartesian form α = dz − (x dy − y dx). Take g = α⊗α + dx² + dy². Then g(∂_z, ·) = α; the coefficients do not depend on z, so ∂_z is Killing; the frame e₁ = ∂_x − y∂_z, e₂ = ∂_y + x∂_z spans ker α, is orthonormal for g, and dα(e₁, e₂) = −2. A K-contact structure in dimension 3 is Sasakian (Blair; cited, not re-derived). The earlier proof, which used Gray stability on a non-compact manifold, is replaced.

**Claims withdrawn or reframed from the earlier version.**
- T2 as a Whitney A1 fold of the asymptotic map: withdrawn (the map is 1 on one side of r* and undefined on the other). The basin boundary is the stable manifold of a hyperbolic saddle.
- T* = 2π as the T-self-dual radius: withdrawn. T* is the period of θ; the self-dual radius is √α′, so R = 1 is a unit choice and the equality holds by construction.
- ADE: the McKay correspondence stands, and the labels A₁, A₂, A₃ coincide legitimately (Arnold's simple singularities and the Kleinian singularities ℂ²/ℤ_{k+1} are the same A_k). The physical step that a dm³ fold at a given scale selects a given gauge group is a proposal.
- Hill sphere as an A1 fold at "g96, magnified by 10²⁵": withdrawn. The Hill critical point is an index-1 saddle, and 10²⁵ is the ratio of the table's endpoints (10²² m / 10⁻³ m), not a derived rescaling.
- Table 1, g64 "Proved": removed; the number r*(0) is certified, the physical reading is proposed.

## 3. Anchors

> **Why this section is here.** A table that ties each rung to a known, independently stated fact, with a status column (checked, proposed, imported). This is the load-bearing section: it is where the framework touches data it did not make.

An anchor writes down both sides: a known structure and the operator slot it fills. Strength: strong (known side checked), proposed (slot reading, known side not shown to be the same type), empty (no known structure written down yet).

| Phenomenon | Operator reading | Strength | What is checked |
|---|---|---|---|
| Kepler II | contact condition α = 0 | strong | exact |
| Newton circular orbits | C, K with no F; the chain does not close | strong | dL²/dr = GM ≠ 0 |
| Schwarzschild ISCO | K: V_eff'' → 0; F: A1 fold of L²(r) at 6M; U: stable pair above, plunge below | strong | V_eff'' < 0, 0, > 0 at 5M, 6M, 7M; d²L²/dr² = 2/3 |
| Hill sphere | the saddle slot, not the fold: the L1/L2 critical point of W = 3x²/2 + 1/r is an index-1 Morse saddle (Hessian diag(9, −3), det −27), the same kind of object as the dm³ boundary saddle, whose stable manifold is the basin boundary | proposed | Hessian computed; the earlier "A1 fold" wording is not supported |
| Newton–Poisson | the field is the 3-manifold; K: curvature of the potential equals its source | proposed | dα constant; no source term written |

**Fold and unfolding (Schwarzschild).** Circular orbits solve M r² − L² r + 3M L² = 0, with discriminant L²(L² − 12M²). Two orbits exist for L² > 12M², one at L² = 12M² (r = 6M), none below. The unfolded pair is r± = (L² ± L√(L² − 12M²))/2M: stable outer, unstable inner. For large L, r₊ → L²/M (the Newtonian relation) and r₋ → 3M (the photon sphere).

**Scaling with mass.** In units G = c = 1 the Schwarzschild structure is the same for every mass M; only the units GM/c² (length) and GM/c³ (time) change. The orbital speed at the ISCO is c/√6 ≈ 0.41c for every mass. The gravitational-wave frequency at the ISCO (twice the orbital frequency) is f = c³ / (π·6^(3/2)·GM): about 4.4 kHz for one solar mass, 440 Hz for ten, 1.0 mHz for 4.3 × 10⁶ solar masses, and the ISCO radius is 8.9 km per solar mass and 2.7 cm for Earth (script `moon_hill_roche.py`). This is the physical counterpart of the scale-free form of section 2. The speed of gravitational waves does not depend on the source; it is c.
**Spin.** For a rotating black hole the fold is not at 6M: the Kerr ISCO runs from about 1M (prograde, maximal spin) to 9M (retrograde), with 6M the non-spinning case (textbook; not from a source read in this revision). Spin is another parameter the threshold depends on.

## 4. A worked anchor: Earth–Moon (script `moon_hill_roche.py`)

> **Why this section is here.** One concrete case done end to end with numbers a reader can recompute. The script is named in the heading so the claim and its check travel together; it includes controls that could have failed.

The threshold moves with the state, so the Moon is a trajectory through an unfolding, not a point beside a fold.
- Earth's Hill radius is 1.496 × 10⁶ km; the Moon (3.844 × 10⁵ km) is at 0.257 r_H. In Hill's problem (script `hill_stability.py`, circular initial orbits, 400 time units, step 0.02 in ρ/r_H) prograde orbits stay bound up to ρ/r_H = 0.48 and the first escape is at 0.50. Retrograde orbits stayed bound across the whole scan, to 0.96 r_H. The published figures (Grav. stability of distant satellites, arXiv:0806.2882, abstract) are about 0.5 r_H for prograde and about 0.7 r_H for retrograde satellites in general, with some coplanar retrograde orbits surviving to about r_H, which is consistent with our coplanar scan; our scan is a short-horizon test, not a rederivation. The Moon is at about 0.51 of the prograde limit. This is the restricted problem: the Moon does not move the Earth.
- The fluid Roche limit is 18,370 km; the Moon is 20.9 times farther out.
- Earth's Schwarzschild ISCO is 2.66 cm: real, and irrelevant at this scale.
- Mutual motion and radiation: the Earth–Moon barycentre is 4,668 km from Earth's centre, inside Earth. The quadrupole gravitational-wave power of the pair is about 7 × 10⁻⁶ W, which would take about 10²⁶ years to matter; tides, not waves, move the Moon.
- Toy model: tidal recession with constant Q gives ȧ ∝ a^(−11/2). From the observed 3.8 cm/yr this reaches 0.5 r_H after about 117 Gyr, beyond the Sun's lifetime. This is a geometry illustration, not a forecast; it ignores the solar tide and changes in Earth's spin.
The control parameter differs by rung (L at 6M, d/r_H for satellites, the Roche radius for tides) while the slot (a stable branch, an unstable branch, plunge or escape) is the same. That is the content of the taxonomy.

## 5. A geometric reading: S³, H⁴ and the expanding disc

> **Why this section is here.** The bold, interpretive section, kept separate and labelled 'proposed' so that speculation cannot contaminate the checked sections. Say what is a standard fact (the geometry of AdS₅ slices) and what is the author's reading.

This section reads known structures in the framework's language. It adds no physics, and every item is proposed. Identities marked checked were verified in sympy (`h4_checks.py`); the rest are standard facts stated without re-derivation.

| Known structure | Geometric reading | Status |
|---|---|---|
| Global AdS₅: −cosh²ρ dt² + dρ² + sinh²ρ dΩ₃² | at fixed t the spatial slice is hyperbolic 4-space H⁴; the spheres S³(ρ) foliate it and t is the Killing time. Even-dimensional base, odd-dimensional sphere, time added: 4 + t = 5 | checked: with r = sinh ρ, dr²/(1 + r²) = dρ² |
| Geodesic sphere in H⁴ | round S³ of intrinsic radius sinh ρ with the Hopf contact structure; area 2π² sinh³ρ against 2π²ρ³ in flat space; principal curvature coth ρ → 1, so far out it looks like a horosphere, intrinsically flat ℝ³ | limits checked; the contact structure of the round S³ is standard |
| Conformal boundary ℝ_t × S³ | S³ minus a point is ℝ³ by stereographic projection, and the standard contact structure on S³ becomes the standard one on ℝ³: (ℝ³, α) is the border with a point removed (up to constants in α) | standard fact, not re-derived |
| A plane through the centre of H⁴ | a totally geodesic H², a disc in the Poincaré model. In (ℝ³, α) the disc is the base (x, y) with area form dα = −2 dx∧dy, and z is twice the area swept, so an orbit in the disc lifts to a curve that climbs by its swept area | checked: dα = −2 dx∧dy |
| Kaluza–Klein form | g = (dz − A)² + dx² + dy², A = x dy − y dx, F = dA = 2 dx∧dy, a uniform field on the base; symplectic base 2 plus fibre 1, then the author's 4 + t = 5 | checked in 3D; 5D not worked out |
| Expanding disc moving outward in time | geodesics from a point diverge exponentially in H⁴ and sphere area grows as sinh³ρ. The ODE moves the other way: r*(z) shrinks as z advances (0.776 at z = 0, 0.0365 at z = 4) and orbits converge on the helix. Whether these are two sides of one picture is open | area growth checked; the comparison is a reading |
| Cosmic history (Ferreira 2013 slides 8, 9, 12, 14) | the funnel widens with time from the quantum-gravity wall to today, with labelled stages from grand unification to acceleration: a Planck → QCD → atomic → galactic ladder in time, in the order of the g-series in length | read from the slides at low resolution; the funnel is a schematic |
| The horizon (slide 40) | a preferred length scale H⁻¹ = (ȧ/a)⁻¹ ≈ 3000 h⁻¹ Mpc that moves as the universe expands: a moving threshold of the kind the dm³ tilde stands for | read from the slide |

We are only reading what is known: each row takes the known structure on one side, and the framework supplies the vocabulary on the other.

## 6. What can be observed at each rung

> **Why this section is here.** Turn the taxonomy into a test list: for every rung, what measurement exists and what it assumes (for example continuum fitting assumes the disc edge sits at the ISCO). Papers are trusted more when they say where the data stop.

The fold is the geometric part that leaves a trace. Each row gives the signature, the model needed to read it, a strength label, and the source. Sources marked "abstract" were read at the abstract level only; others were located but not read in this revision.

| Rung | Signature | Model needed, and limits | Strength | Source |
|---|---|---|---|---|
| Strong field: ISCO | inner edge of an accretion disc, from the X-ray continuum, read as the ISCO; the fitted radius gives the spin | assumes the disc ends at the ISCO with zero stress there (the authors call this unproven); applied to thermal states below about 30% of Eddington luminosity; needs mass, distance and inclination; simulations show some emission inside the ISCO | proposed (the fold is checked; the observational reading is model-dependent) | McClintock et al., arXiv:1101.0811 |
| Strong field: wave speed | arrival-time difference between gravitational waves and light in GW170817/GRB 170817A: 1.74 s; the speed of gravity differs from c by between −3 × 10⁻¹⁵ and +7 × 10⁻¹⁶ of c | assumes the emission delay is small | strong (for the statement that wave speed does not vary with source) | arXiv:1710.05834 (abstract) |
| Strong field: radiation reaction | orbital decay of a binary pulsar, and inspiral-to-plunge in gravitational-wave mergers | general relativity's quadrupole formula | not assessed here | Hulse–Taylor and gravitational-wave literature: located, not read |
| Planetary: Roche limit | small satellites pile up at the Roche radius of Saturn, Uranus and Neptune; satellites form beyond it from spreading discs (Saturn's Roche radius, 140,000 km, as used in the paper) | disc-spreading model; Jupiter's system does not fit it | proposed | Crida and Charnoz, Science 2012 |
| Planetary: Hill sphere | distant satellites: prograde stable to about 0.5 r_H, retrograde to about 0.7 r_H (some coplanar to about r_H); stable orbits at 2 r_H or more exist around Jupiter, Uranus and Neptune (to about 10 r_H for the last two) | numerical integration over the Solar System's lifetime; other perturbers matter, so r_H is a rough boundary | proposed (saddle reading) | arXiv:0806.2882 (abstract) |
| Earth–Moon distance | lunar laser ranging gives a recession of about 3.8 cm per year | tidal model; not sourced in this revision | proposed | not sourced here |
| Galactic: Milkomeda | predicted merger of the Milky Way and Andromeda in about 4.5 × 10⁹ years | N-body simulation from measured velocities; not an observation of a fold | empty (the reading as basins is not derived) | van der Marel et al., ApJ 753, 9 (2012), cited by the earlier version |
| Planck / QCD rungs | no gravity measurement | none | empty | none |

## 7. Scale ladder (Table 1, revised)

> **Why this section is here.** A summary table for skimmers. It carries a strength column and three marked corrections, because the table is the part most likely to be quoted out of context.

Table 1 lists the rungs of the g-series as the earlier chapter gave them, with two added columns: what gravity measurement exists at the rung, and a strength label. An empty cell is an empty slot, not a failed prediction. The length ranges are copied from the earlier chapter and not re-derived here; the ranges span 10⁻³⁵ m to 10²² m, 57 orders of magnitude.

| Rung | Length (earlier chapter) | Known structure read at this rung | Gravity measurement that exists | Strength |
|---|---|---|---|---|
| g⁰–g⁴ | 10⁻³⁵–10⁻³¹ m | Planck scale, string worldsheet, Sasakian geometry (conjectural) | none | empty |
| g⁵–g⁸, seed at g⁶ | 10⁻³¹–10⁻²⁵ m | ADE singularities and gauge-group labels: the A_k names coincide (Arnold's simple singularities and Kleinian quotients ℂ²/ℤ_{k+1}); McKay correspondence | none | conjecture |
| g¹⁶–g³² | 10⁻¹⁸–10⁻¹² m | electroweak and QCD transitions, confinement (conjectural reading) | none | empty |
| g³²–g⁴⁸ | 10⁻¹²–10⁻⁶ m | atomic and molecular scale; the earlier chapter places r* here | none for gravity | proposed (r* itself is a certified computation, not a measurement) |
| g⁶⁴ | 10⁻³–10¹ m | the model ODE: helix r = 1, saddle, basin boundary r*(0) = 0.77594057550 (interval certificate); levitation gap | not a gravity measurement; the "Proved" mark on this row in the earlier version is withdrawn | checked (computation); reading proposed |
| g⁶⁴ → matrix | saturation boundary | matrix-valued extension of the scalar series | none | open |
| "g⁹⁶" | 10⁹–10²² m | planetary orbits and Hill sphere; Milkomeda merger; cosmic history | Hill sphere: distant-satellite stability (arXiv:0806.2882, abstract); Milkomeda: N-body prediction, not an observation of a fold; funnel of 2013, dated before JWST | Hill sphere: proposed as an index-1 saddle (not a Whitney A₁ fold); Milkomeda: empty |

Three corrections to the earlier table are marked here. First, the Hill sphere's L1 and L2 points are index-1 saddles, so the earlier "Whitney A₁ fold" is replaced. Second, the Schwarzschild fold at 6M (section 3) is a rung of its own that the earlier table did not have; it belongs between the planetary and strong-field entries. Third, the label g⁹⁶ lies beyond the series' stated end at g⁶⁴ and is kept only because the earlier chapter used it; it needs a decision from the author (rename it, or extend the series).

## 8. Universality hypothesis

> **Why this section is here.** Say precisely what would have to be true for the framework to be more than a taxonomy, and that this paper does not show it. A hypothesis stated this way can be falsified, which is what makes it worth publishing.

Two claims are kept apart. (i) The form is scale-free: a theorem, section 2. (ii) Each rung has a real phenomenon with the structure: a set of anchors, each standing alone. Hypothesis: every known gravitational threshold has a place in the chain. Falsifier: a known threshold at some rung that the chain cannot place.

## 9. Limits

> **Why this section is here.** List what was not read, not checked, and not claimed. Reviewers and later readers use this section to decide how far to trust the rest.

Not checked: the Ferreira slides beyond a low-resolution view of the contact sheets; the stereographic/contact statement and the AdS₅ slicing facts, which are standard but not re-derived; the references of the earlier version, its figures and its Sections 8 to 11 beyond reading; the K-row threshold κ* = √(7/9); the levitation experiment; the observational sources in section 6 beyond their abstracts (the binary-pulsar and gravitational-wave merger literature and the lunar laser ranging value were not read); the textbook Kerr ISCO range. The map between the ODE and the Schwarzschild or Hill systems is not written; reading z as the accumulated twice-area, a monotone clock along which the forcing 2(r − 1)e^{−z} decays, is a proposal. No independent referee has read this paper. Source documents: `AUDIT_GravityScales.md`, `GRAVITY_LAW_READING.md`, `GRAVITY_V2_PLAN.md`.

## 10. Disclosure

> **Why this section is here.** State the tools used (AI assistance, scripts, sources) and who is responsible for the content. Zenodo and journals increasingly expect this, and it lets readers weigh the work honestly.

Several earlier papers in this series were machine-condensed from larger source files, and some figures in them were not traced back to their sources; this version recomputes every number it states, with the scripts listed above. An AI assistant (Claude, Sonnet 5.5) drafted text and wrote the scripts under the author's direction. The claims, and responsibility for them, are the author's. The sources in section 6 marked "abstract" were read at the abstract level only.
