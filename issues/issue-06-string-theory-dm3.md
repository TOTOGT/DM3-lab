## String theory (NS-NS / RR sectors): complete dm³ identification and Lean axiom check

**Labels:** `lean`, `string-theory`, `dm3`, `mappings`, `research`

---

### Summary

`mappings/domain_mappings.md` sketches the string theory instantiation of the TOGT operator chain (NS-NS / RR sectors, Calabi-Yau compactification, conifold transitions). This instantiation needs to be:

1. Completed with explicit dm³ metric values
2. Stated as a formal `Dm3Triple` instance in Lean 4
3. Checked against the canonical invariants `(T*, μ_max, τ) = (2π, -2, 2)`

---

### Background

Current mapping in `domain_mappings.md`:

| Operator | String instantiation |
|---|---|
| **C** | Compactification: 10D → 4D on Calabi-Yau manifold |
| **K** | Moduli stabilization: curvature of landscape potential |
| **F** | Topology change: conifold transition (rank-1 degeneration of holomorphic 3-cycle) |
| **U** | Flux stabilization: Gukov-Vafa-Witten superpotential selects stable vacuum |

**Partial dm³ identification:**
> *The axio-dilaton field τ_IIB plays the role of the embodiment threshold. The stability radius ε₀ = 1/3 corresponds to the perturbative regime boundary.*

Missing: explicit values for `T*` and `μ_max` in the string theory context.

---

### Scope of this issue

- [ ] **Research:** identify the string-theoretic quantities corresponding to `T*` (limit cycle period) and `μ_max` (maximal Lyapunov exponent). Candidates:
  - `T*` ↔ period of the axio-dilaton modular orbit?
  - `μ_max` ↔ rate of moduli runaway?
- [ ] Update `mappings/domain_mappings.md` with the complete table including `T*` and `μ_max` values and their string-theoretic sources
- [ ] Add to `lean/Main.lean` (or a new `lean/StringTheory.lean`):
  - A `stringTheoryTriple : Dm3Triple` instance with the identified values
  - A check that `stringTheoryTriple.mu_max < 0` and `stringTheoryTriple.tau > 0`
- [ ] Honest epistemic note: mark as **conjectured** if the identification is not yet derived from first principles

---

### Acceptance criteria

1. `mappings/domain_mappings.md` has a complete string theory row with all four `(T*, μ_max, τ, ε₀)` values sourced.
2. `stringTheoryTriple` type-checks in Lean 4.
3. The epistemic status (empirical / conjectured / proposed) is clearly stated.
4. `lake build` passes.

---

### References

- `mappings/domain_mappings.md` — partial string theory mapping
- `lean/Main.lean` — `Dm3Triple`, `canonicalTriple`
- Gukov, Vafa, Witten (2000) — *CFT and D-Branes*, superpotential formula
- KKLT (Kachru, Kallosh, Linde, Trivedi 2003) — flux compactification
- Mathlib4 `NumberTheory.Modular`
