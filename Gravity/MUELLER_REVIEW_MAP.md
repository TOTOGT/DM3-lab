# Mueller's paper and your dm3 gravity work: what I connected, why, and how far each link goes

Prepared 20 Nov 2026. Internal working note. It is not part of the referee audit of Mueller's paper. The audit is a separate package: https://totogt.github.io/DM3-lab/referee/mueller-lorentz-slope/index.html (files in `referee/mueller-lorentz-slope/` in this repository), which links back to this note. Nothing here has been sent to anyone.

## What this note is

While checking Mueller's paper in Lean, sympy and numbers, I compared it with your gravity work and wrote a table of possible connections. That table gave no reasons, no links and no indication of how strong each connection was. This note replaces it. For each pairing it says what Mueller's paper claims and where, what your work says and where, why I put them side by side, how strong the link is, and what would settle it.

A word on strength, used throughout:

- **Shared fact.** Both sides state the same mathematical fact. This can be checked.
- **Structural analogy.** The two share a shape (for example, both have a "fold"), but nobody has written down a map between them. This is a suggestion only.
- **Coincidence to avoid.** The same symbol or number appears and I recommend not connecting them.

## Sources

Mueller: A. Mueller, *The Lorentz Factor as the Slope of an Additional Spatial Coordinate: Embedding, Painlevé–Gullstrand Flow, and the Issue Of Simultaneity*, Zenodo v1, 16 Nov 2026 (equation and section numbers below are the paper's). What I checked is in `referee/mueller-lorentz-slope/LEDGER.md`, with files `MuellerChecks.lean`, `check_sympy.py` and `check_numbers.py` beside it. Sections of Mueller's paper I did not read are listed in that ledger.

Your work, with links:

- *Gravity Across Scales* (the paper): https://totogt.github.io/geometry/chGravity-scales.html. It contains T1–T4, the scale ladder (Table 1), Conjecture 9.1 (Hill sphere as a g96 fold), Open Problem 11.4 (galactic fold radius), and the empirical-grounding list in §12.
- WP56, *Special Relativity as Contact Geometry*: https://totogt.github.io/geometry/book7/wp56-special-relativity.html. Its §2 treats the Lorentz boost as a hyperbolic rotation with γ = cosh φ and v/c = tanh φ.
- WP57, *Causal Integration and the Milkomeda transition*: https://totogt.github.io/geometry/book7/wp57-causal-integration.html. It states Open Problem O4 (the galactic fold radius).
- WP58, *r\*\_galactic: a derivation attempt*: https://totogt.github.io/geometry/book7/wp58-galactic-fold.html. It answers O4 tentatively: r\*(ε) for several couplings, the identification ε_gal = ν/κ at the disc scale radius, and a Milky Way value of about 2.5 kpc. It lists the galactic identification (its O.4.2) as the unproved step.
- WP59, *Dark Matter Lensing*: https://totogt.github.io/geometry/book7/wp59-dark-matter-lensing.html. A different galactic-scale claim, about sub-halo density profiles. I did not compare it with Mueller's paper.
- The Ferreira and Hawking–Ellis maps in this folder (`FERREIRA_REVIEW_MAP.md`) use the same format.

## The connections, one at a time

### 1. The Lorentz factor as a slope: a shared fact

- **Mueller.** §2.2 and eqs (22)–(27): define the extra coordinate y by ∂ₓy = βγ, so that γ = √(1+(∂ₓy)²). Checked: Lean theorems `gamma_eq`, `sx_sq`.
- **Your work.** WP56 §2: γ = cosh φ and v/c = tanh φ, where φ is the rapidity.
- **Why I paired them.** Together these give βγ = tanh φ · cosh φ = sinh φ, so Mueller's slope ∂ₓy is the sinh of the rapidity and his γ is the cosh. Mueller does not say this in those words. I proved it in Lean (`slope_is_sinh`). WP56 already contains both ingredients, so Mueller's construction is a geometric picture of something your chapter treats as a hyperbolic rotation.
- **Strength.** Shared fact (checked). It does not show the two papers are the same theory: WP56 stays inside Minkowski space, while Mueller adds a spatial coordinate and embeds the space slice as a hypersurface.
- **Suggested use.** A sentence in WP56 noting that the slope of an embedded hypersurface whose tangent has rapidity φ is sinh φ, if you wish to link the two.

### 2. The extra direction in each construction: a structural analogy, not an identification

- **Mueller.** A fourth, flat, non-compact spatial coordinate y; the physical space is a hypersurface in ℝ⁴ (§2.4.3–2.4.4).
- **Your work.** *Gravity Across Scales* §6 and T4: the Reeb field ∂z of the contact form α = dz − r²dθ, identified with the Hopf fibre or the M-theory circle (labelled conjectured).
- **Why I paired them.** Both add one direction and give it a geometric role. That is all they share.
- **Strength.** Structural analogy only. Mueller's direction is spacelike, non-compact and used for embedding; yours is a Reeb direction on a contact manifold. No map between them exists in either paper.
- **What would settle it.** A written map between ℝ⁴ with its hypersurface and the contact manifold (ℝ³, α), and a statement of what y corresponds to. Until then, do not identify the Reeb field with y.

### 3. Circular orbits and the innermost stable orbit: a pointer to a standard fact

- **Mueller.** §2.6 gives L² = GMR²/(R − 3GM/c²) for circular orbits. I checked this in sympy.
- **Your work.** T2 and Conjecture 9.1: r\* is a Whitney A₁ fold of the asymptotic radial map; the Hill sphere is conjectured to be the same kind of fold at g96.
- **Why I paired them.** L² as a function of R has a pole at R = 3GM/c² and a minimum at R = 6GM/c² (set d/dR of R²/(R−3M) to zero). That minimum is the standard innermost stable circular orbit, where the family of circular orbits has a fold (a saddle-node). So "a fold in the radial dynamics" is a known feature of the Schwarzschild solution, and your paper uses the word "fold" for r\*.
- **Strength.** Structural analogy, and a weak one: the ISCO fold is of a family of geodesics; r\* is a fold of a map for a dynamical system, and the two systems have not been related. Mueller's paper only restates a textbook result here and adds nothing to the question.
- **Suggested use.** If your paper discusses the Schwarzschild case, compare r\* and the 6M fold explicitly and state where they differ. The Hawking–Ellis note makes the same suggestion.

### 4. Hubble flow and the galactic fold radius: a possible observable, not a derivation

- **Mueller.** §2.8 (Hubble flow, β_H² = 2Gm/(c²R), the critical density with L = c/H, the Sciama identity). Checked in Lean (`hubble_beta`, `critical_L`) and numerically.
- **Your work.** Open Problem 11.4 / O4 and WP58: the radius at which the galactic attractor's basin ends, proposed in WP58 as r\*(ε_gal)·R_disc, with ε_gal = ν/κ.
- **Why I paired them.** Both ask where a galaxy's gravitational influence gives way to something else. In Mueller's setup the Hubble-flow term and the local binding term trade off at a definite radius. In WP58 the transition is a basin boundary of the contact ODE. A candidate observable for O4 could therefore be the radius where the two terms in Mueller's setup are equal. I have not computed that radius and have not compared it with WP58's 2.5 kpc.
- **Strength.** A suggestion for something to compute. WP58's identification (its O.4.2) is itself unproved, and WP58's 2.5 kpc is a bulge–disc transition radius, a different quantity from a Hubble-flow radius, so the two may simply not be comparable.
- **What would settle it.** Computing Mueller's equal-terms radius for the Milky Way and stating whether it has any relation to the bulge–disc scale.

### 5. The factor 2π: a coincidence to avoid

- **Mueller.** §3: Hypothesis M proposes g₀ = κ′cH₀ with κ′ = 1/2π as a candidate. His own free fit gives g₀/(cH₀) = 0.35, which is a factor of about two above 1/2π.
- **Your work.** The T-duality fixed point T\* = 2π (*Gravity Across Scales* §7), and in WP58 the azimuth θ normalised to 2π.
- **Why I paired them.** The number 2π appears on both sides. That is the only reason.
- **Strength.** Coincidence to avoid. In Mueller's paper 1/2π is a trial normalisation for an acceleration scale; in yours 2π is the period of a limit cycle and the length of the circle in θ. Neither paper derives the other's value.

### 6. Numerical alignments and your empirical-grounding list: a difference in kind

- **Mueller.** Appendix A: characteristic velocities compared with the CMB dipole, a one-parameter fit by the paper's own account. I recomputed them (`check_numbers.py`).
- **Your work.** *Gravity Across Scales* §12: independent measurements anchoring statements (atom traps, ALPHA antimatter gravity, the Milkomeda timescale, and so on).
- **Why I paired them.** Both sections are where a paper says what supports its physical claims.
- **Strength.** A difference to state, not a connection. Your §12 items are measurements; Mueller's alignments are fits. If you ever cite Mueller's alignments, say they are fits and not tests.

### 7. Style of ledger: a suggestion about presentation

- **Mueller's paper** says which results are imported from general relativity and which are derived; my ledger of it is sorted as checked, imported, beyond Mathlib, assumed, and not claimed.
- **Your work.** Chapters that already use MODEL, OPEN and CITED tags (for example WP58's [OPEN] items).
- **Why I paired them.** The ledger format could be applied to §§9–12 of *Gravity Across Scales*.
- **Strength.** Presentation only. It says nothing about the physics.

## What this note does not claim

- That Mueller's paper supports, contradicts or is equivalent to any dm3 result. I found no derivation linking them.
- That the Lean checks of Mueller's algebra say anything about T1–T4 or the g-series.
- That WP58's galactic identification is right or wrong. I did not test it.

## Mistake I made earlier

The first version of this table was added to the public referee page for Mueller's paper, which is meant to be only about his paper. It has been taken off that page and out of its zip, and the two now link to each other instead: the referee page points here under "Related note, kept separate", and this note points back to the referee page above.
