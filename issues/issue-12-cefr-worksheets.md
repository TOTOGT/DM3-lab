## Pedagogical CEFR materials: A2 → C1 worksheet set for the Saturn hexagon example

**Labels:** `documentation`, `education`, `cefr`, `good-first-issue`

---

### Summary

`README2.md` defines four pedagogical levels for TOGT aligned with the CEFR language proficiency scale (A2, B1, B2, C1), using Saturn's hexagon as the running example. This issue produces a complete set of four worksheets — one per CEFR level — ready to use in a classroom or self-study context.

---

### Background

From `README2.md`:

| Level | Task | Saturn example |
|---|---|---|
| A2 | Observe | "The jet bends six times" — label the corners |
| B1 | Explain | "Rossby waves select n=6 by rotation + Coriolis" |
| B2 | Derive | "κ* selects the fold mode via Whitney A₁" |
| C1 | Unify | "Saturn = HPA = market: exact morphisms in dm³-Cat" |

These four levels form a coherent pedagogical arc from raw observation to full abstraction. A worksheet set would make TOGT accessible to students at every level.

---

### Scope of this issue

Add `docs/worksheets/` with four files:

**`docs/worksheets/A2_observe_saturn.md`**
- Diagram of Saturn hexagon (reference `02_saturn_hexagon.svg`)
- 5 observation questions: count corners, measure angles, identify the jet stream
- Vocabulary list: hexagon, jet, atmosphere, corner
- Answer key

**`docs/worksheets/B1_explain_saturn.md`**
- Brief introduction to Rossby waves and the Coriolis effect
- 4 explanation questions: why does rotation select n=6? What is β?
- Simple formula for Rossby wave phase speed (no calculus)
- Answer key

**`docs/worksheets/B2_derive_saturn.md`**
- Introduction to curvature threshold κ* and the Whitney A₁ singularity
- 3 derivation exercises: compute κ* from the Rossby dispersion relation, verify the fold condition
- Requires calculus; references Vallis (2017) for background
- Answer key

**`docs/worksheets/C1_unify_saturn.md`**
- Full dm³ triple `(T*, μ_max, τ) = (2π, -2, 2)` for Saturn
- 2 synthesis exercises: draw the functor diagram linking Saturn, HPA axis, and a financial market; state the Coherence Bridge Theorem in your own words
- Open-ended reflection: what would falsify the morphism claim?
- Partial answer key (open questions)

---

### Acceptance criteria

1. All four worksheets exist in `docs/worksheets/`.
2. Each worksheet includes: learning objectives, questions, and an answer key.
3. The materials are self-contained (reader does not need to read the full paper first).
4. Language complexity matches the CEFR level (A2: simple sentences; C1: technical prose).
5. `02_saturn_hexagon.svg` is referenced where appropriate.

---

### References

- `README2.md` — CEFR table and Saturn hexagon description
- `02_saturn_hexagon.svg` — diagram to use in A2 worksheet
- `mappings/domain_mappings.md` — operator chain for B1/B2/C1
- CEFR descriptors: https://www.coe.int/en/web/common-european-framework-reference-languages
- Vallis, *Atmospheric and Oceanic Fluid Dynamics*, Cambridge 2017 (B2/C1 reference)
