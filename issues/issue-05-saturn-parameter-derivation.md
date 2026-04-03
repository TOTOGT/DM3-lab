## Saturn hexagon: independent derivation of μ_max, ω, β, κ* from atmospheric data

**Labels:** `research`, `saturn`, `dm3`, `open-question`, `empirical-validation`

---

### Summary

`README2.md` raises the following open question about the Saturn hexagon instantiation:

> **Open question:** Are the parameters μ_max, ω, β, κ* derived independently from atmospheric data, or fitted post-hoc?

This is the most important empirical test of the TOGT framework. This issue tracks the work needed to answer it definitively and document the result.

---

### Background

The TOGT claim for Saturn's north polar hexagon is:

| Operator | Saturn instantiation |
|---|---|
| **C** | 3D atmosphere compresses to quasi-2D jet layer |
| **K** | Rossby wave curvature selects wavenumber n=6 |
| **F** | Whitney fold locks the six sharp corners |
| **U** | Gradient descent on Φ yields the 40+ year fixed point |

The **canonical dm³ triple** is `(T*, μ_max, τ) = (2π, -2, 2)`.

The question is: can `μ_max = -2`, `τ = 2`, and `ε₀ = 1/3` be derived **a priori** from:
- Saturn's rotation rate `ω_Saturn = 1.638 × 10⁻⁴ rad/s`
- Atmospheric beta parameter `β = ∂f/∂y`
- Rossby wave dispersion relation
- Observed jet velocity profile

...without first knowing the answer?

---

### Scope of this issue

- [ ] Add a notebook or script `simulations/saturn_hexagon.py` (or `.ipynb`) that:
  - Imports Saturn atmospheric parameters from a public source (e.g., NASA PDS, Cassini CIRS)
  - Computes the dm³ triple `(T*, μ_max, τ)` from first principles using Rossby wave theory
  - Compares the derived values to the canonical `(2π, -2, 2)`
- [ ] Add a section to `mappings/domain_mappings.md` documenting the derivation with equations
- [ ] State explicitly whether the match is **a priori** (derived) or **post-hoc** (fitted)
- [ ] If post-hoc: document what additional constraints would make it a priori

---

### Success criteria

The issue is **resolved** when one of the following is documented with equations and data sources:

**A.** The parameters `μ_max, τ` can be derived from published atmospheric data *before* comparing to the canonical triple → strong empirical support for TOGT.

**B.** The parameters were selected to match the canonical triple → document this honestly and specify what a falsifiable prediction would look like.

---

### References

- `README2.md` — Saturn hexagon section with the open question
- `mappings/domain_mappings.md` — current mapping table
- `02_saturn_hexagon.svg` — diagram
- Cassini data: https://pds-atmospheres.nmsu.edu/
- Rossby wave theory: Vallis, *Atmospheric and Oceanic Fluid Dynamics*, Cambridge 2017
- Fletcher et al. (2018), *Nature Communications* — Saturn hexagon morphology
