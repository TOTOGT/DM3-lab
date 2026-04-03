## Martian colony dm³ simulation: closed-loop life support stress model

**Labels:** `simulation`, `martian-colony`, `dm3`, `volume-IV`, `enhancement`

---

### Summary

`mappings/domain_mappings.md` outlines the Martian colony architecture application of the dm³ framework (Volume IV, forthcoming). This issue implements the first concrete simulation: a closed-loop life support stress model using the TOGT operator chain.

---

### Background

From `domain_mappings.md`:

> - **C:** Resource compression — metabolic degrees of freedom reduced to a minimal viability set  
> - **K:** Stress accumulation — physiological/engineering loads driven toward critical threshold  
> - **F:** System fold — failure mode onset (atmosphere breach, crop failure, radiation event)  
> - **U:** Recovery branch selection — redundant system activation, biological adaptation  
>
> The allostatic unification law `τ₁₂ ≤ min(τ₁, τ₂)` governs coupled subsystems.

The Python simulation framework in `simulations/simple_to_operator.py` already implements C→K→F→U as graph transformations. The Martian colony model extends this to a **coupled dynamical system** with multiple subsystems.

---

### Scope of this issue

Add `simulations/martian_colony.py` with the following model:

**System state:**
- `atmosphere`: pressure, CO₂ fraction, O₂ fraction (3 degrees of freedom)
- `crew_physiology`: allostatic load (1 scalar, HPA axis)  
- `power_supply`: available watts (1 scalar)
- `food_production`: kg/day (1 scalar)

**Operator chain applied to the coupled system:**
- `C`: reduce to minimal viability variables (drop non-critical sensors)
- `K`: accumulate daily stress increments per subsystem
- `F`: detect fold events (subsystem exceeds threshold → failure mode)
- `U`: activate recovery protocol (redundant subsystem, crew adaptation)

**dm³ metric output:**
- `τ₁₂ ≤ min(τ_atmosphere, τ_crew)` verified numerically
- Plot of allostatic load over simulated 30-day mission arc

---

### Acceptance criteria

1. `python simulations/martian_colony.py` runs without errors.
2. Output includes a stress trajectory plot saved to `outputs/martian_colony_stress.png`.
3. The `τ₁₂ ≤ min(τ₁, τ₂)` allostatic unification law is computed and printed.
4. Code is documented and follows the style of `simple_to_operator.py`.

---

### References

- `mappings/domain_mappings.md` — Martian colony section
- `simulations/simple_to_operator.py` — operator chain template to follow
- `docs/index.md` — dm³ canonical invariants
- Basner et al. (2014), *PLOS ONE* — HI-SEAS Mars simulation stress data
- NASA Mars Design Reference Architecture 5.0 — life support parameters
