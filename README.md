# AXLE – Topographical Orthogenetics Proofs & Extensions
AXLE toy machine fruit fly 🪰

Formal verification hub and extensible repository for **Topographical Orthogenetics (TO)** and **Topographical Orthogonal Generative Theory (TOGT)**.

## Core Focus
- Lean-verified proofs for scaling hierarchies (g⁵/g⁶ → hyper-Mahlo regenerations)
- Operator chain implementations & mappings: **C → K → F → U** across scales
- Nth-degree reconfiguration algorithms & community extensions
- Bridges: plasma instabilities → biological morphogenesis → dm³ systems → Martian colony architecture → toy brain models (fly 🪰 connectome as starting point)
- **Discrete dm³ bridges**: Saturn hexagon geometry → Collatz shortcut map → dm³ canonical invariants

## Current Status

### Main.lean (TOGT core — zero sorry, zero axioms)
All Volume IV theorems formalized: Mahlo-like hierarchy, club filter stationarity, g⁶ crystal invariants, regeneration unboundedness.

### DiscreteDM3Bridge.lean (Collatz ↔ dm³ bridge chain)

Eight bridges connecting Saturn hexagon empirical geometry to the Collatz shortcut map via the dm³ canonical triple:

```
Saturn hexagon (empirical, m = 6)
  → phase space 12-dimensional  [C(12,2) = 66]
  → C(12,2)/2 = 33 = g⁶ layer count  [Bridge 2, proved]
  → g⁶ = 3 × 11, crystal seed  [Bridge 3, proved]
  → trivial cycle {1,2,4}, period = 3  [Bridge 4, proved]
  → geometric mean of T*(n)/n = 3/4  [Bridge 5, proved]
  → log₂(3/4) = log₂ 3 − 2 ≈ −0.415 = μ_max analogue  [Bridge 7, proved]
  → c = 3 is the unique odd integer with c/4 < 1  [Bridge 8, proved]
```

**The key result (Bridge 5):** The geometric mean of the Collatz shortcut map T\*(n)/n converges to exactly **3/4** for c = 3 (and to 5/4 for c = 5). This is the Terras/Lagarias theorem. It separates c = 3 from every other odd integer: the ratio is c/4, and 3 is the unique odd value below 4.

#### AXLE Target 5 — Three Formal Gaps

The file `lean/DiscreteDM3Bridge.lean` formally states the three residual gaps with `sorry`:

| Gap | Statement | Why it remains open |
|---|---|---|
| **A — Smoothness** | The Collatz map extends to a smooth dm³ vector field | Requires an interpolation construction to a compact manifold |
| **B — Lyapunov pointwise vs. average** | Every Collatz orbit eventually reaches 1 | Equivalent to the Collatz conjecture itself |
| **C — Categorical extension** | Functor DiscreteCollatzCat → Dm3Cat exists | Functor construction is the content of AXLE Target 5 |

The paper does not claim to prove the Collatz conjecture. It claims something prior: **the conjecture is visible from within the crystal geometry before it is axiomatic within it.** The sorry labels mark precisely where visibility ends and proof begins.

## Repository Structure
- `/lean/Main.lean`                  → TOGT core: Mahlo hierarchy, g⁶ invariants (zero sorry)
- `/lean/DiscreteDM3Bridge.lean`     → 8 bridges: Saturn hexagon → Collatz → dm³ (3 sorry gaps)
- `/mappings/`                       → C→K→F→U across six domains
- `/simulations/`                    → Python toy models (fly connectome + TO operators)
- `/docs/`                           → Excerpts, references, book ties

## Related Work
- Book: *Applications of Generative Orthogonal Matrix Compression Science* (Vol. IV, Principia Orthogona)
- Zenodo: [10.5281/zenodo.19117400](https://doi.org/10.5281/zenodo.19117400)
- HAL preprints: hal-05555216, hal-05559997
- X: [@unitedWeStreamU](https://x.com/unitedWeStreamU) (search "AXLE" for threads)

## Contributing
Want to add files to the community — including from your phone? See [CONTRIBUTING.md](CONTRIBUTING.md) for a step-by-step guide to uploading files via the GitHub mobile app.

Contact: Pablo Nogueira Grossi | pablogrossi@hotmail.com | G6 LLC · Newark, NJ · 2026 | ORCID: 0009-0000-6496-2186