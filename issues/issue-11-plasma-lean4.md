## Domain mapping: plasma instability formalization in Lean 4

**Labels:** `lean`, `plasma`, `formal-verification`, `mappings`, `help-wanted`

---

### Summary

`mappings/domain_mappings.md` contains the plasma instability instantiation of the TOGT operator chain (magnetic reconnection, Harris current sheet, X-point). This mapping needs a matching Lean 4 formalization analogous to the biological morphogenesis path already sketched for the connectome.

---

### Background

Current plasma mapping in `domain_mappings.md`:

| Operator | Plasma instantiation |
|---|---|
| **C** | Magnetic flux compression in reconnection events |
| **K** | Current sheet thinning: curvature accumulation toward κ* |
| **F** | Reconnection onset: rank-1 loss at X-point |
| **U** | Post-reconnection relaxation: Taylor relaxation to minimum-energy state |

**dm³ identification (partial):**
> *The reconnection rate γ plays the role of μ_max. The Sweet-Parker length corresponds to the stability radius ε₀ = 1/3.*

What is missing: explicit values for `T*` and `τ` in the plasma context, and a Lean `Dm3Triple` instance for plasma reconnection.

---

### Scope of this issue

**Part 1 — Complete the mapping documentation:**
- [ ] Update `mappings/domain_mappings.md`: add a complete table row for plasma with all four `(T*, μ_max, τ, ε₀)` values
- [ ] Identify `T*` in plasma: is it the Alfvén crossing time? The current sheet oscillation period?
- [ ] Identify `τ` in plasma: is it `√(γ_Alfvén / γ_resistive)`?
- [ ] Add literature source for each identification

**Part 2 — Lean 4 formalization:**
- [ ] Add to `lean/Main.lean` (or `lean/PlasmaInstability.lean`):
  ```lean
  -- Plasma dm³ triple (reconnection rate γ ↔ μ_max)
  def plasmaTriple : Dm3Triple where
    T_star  := _  -- Alfvén time, to be determined
    mu_max  := _  -- reconnection rate, to be determined
    tau     := _  -- Sweet-Parker ratio
    stable  := by norm_num
    tau_pos := by norm_num
  ```
- [ ] Prove `plasmaTriple.mu_max < 0` and `plasmaTriple.tau > 0`
- [ ] Add a comment explaining the physical meaning of each field

---

### Acceptance criteria

1. `mappings/domain_mappings.md` has a complete plasma dm³ identification with sources.
2. `plasmaTriple` type-checks in Lean 4.
3. Epistemic status (empirical / conjectured) is clearly stated for each value.
4. `lake build` passes.

---

### References

- `mappings/domain_mappings.md` — plasma mapping to extend
- `lean/Main.lean` — `Dm3Triple`, `canonicalTriple`
- Sweet (1958), Parker (1957) — Sweet-Parker reconnection model
- Priest & Forbes, *Magnetic Reconnection*, Cambridge 2000
- Birn & Priest (eds.), *Reconnection of Magnetic Fields*, Cambridge 2007
