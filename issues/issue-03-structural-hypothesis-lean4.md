## Lean proof: Structural Hypothesis (SH) — mutual orthogonality of perpendicular components

**Labels:** `lean`, `formal-verification`, `structural-hypothesis`, `volume-VI`

---

### Summary

The **Structural Hypothesis (SH)** — mutual orthogonality of the perpendicular components of the TOGT operator — is currently stated as *assumed* in `README2.md`:

> *Structural Hypothesis SH: mutual orthogonality of perpendicular components — assumed, formal verification deferred to Volume VI.*

This issue tracks the formal verification of SH in Lean 4. Closing this issue is equivalent to the main mathematical contribution of Principia Orthogona Volume VI.

---

### Background

In the TOGT framework, the generative operator `𝒢 = U ∘ F ∘ K ∘ C` acts on a Riemannian manifold `(X, g)`. The Structural Hypothesis states:

> At each fold point `x*` where `‖κ‖ = κ*`, the stable and unstable manifolds of the fixed point of `𝒢` are mutually orthogonal with respect to the metric `g`.

This is the geometric condition that guarantees the Whitney A₁ singularity is non-degenerate and that `U` can select a unique stable branch (i.e., that the unfold is well-defined).

Without SH, the Convergence theorem (Banach fixed point with contraction constant `κ ≤ √(7/9) ≈ 0.882`) may fail.

---

### Current status in `lean/Main.lean`

The structures `GenerativeManifold`, `FoldOp`, and `UnfoldOp` are defined. The `UnfoldOp.stable_branch` field asserts existence of a fixed point iterate but does **not** assert orthogonality of stable/unstable manifolds.

---

### Scope of this issue

- [ ] Define `StableManifold` and `UnstableManifold` as `Set M.carrier` for a fixed point of `GenerativeOp`
- [ ] State `StructuralHypothesis` as a `def` or `structure` asserting `⊥` (orthogonality under `M.metric`)
- [ ] Attempt a proof for the toy model on `M = S × ℝ` with contact form `α = dz - r² dθ`
- [ ] If a full proof is not yet possible, add an `axiom StructuralHypothesis` with an honest comment noting it is the key open assumption
- [ ] Add a theorem showing that `StructuralHypothesis → UnfoldOp.unique_branch` (uniqueness of the stable branch under SH)

---

### Acceptance criteria

1. `StructuralHypothesis` is stated in Lean 4 in a way that a reviewer can understand and evaluate.
2. Either a proof or an explicit `axiom` declaration (with comment) is present.
3. The logical dependency — SH implies unique stable branch — is formalized.
4. `lake build` passes.

---

### References

- `README2.md` — SH statement and epistemic status table
- `lean/Main.lean` — `UnfoldOp`, `FoldOp`, `GenerativeManifold`
- `docs/index.md` — canonical invariants `(T*, μ_max, τ) = (2π, -2, 2)`
- Mathlib4 `Analysis.InnerProductSpace.Orthogonal`
