## Lean proof: hyper-Mahlo regeneration — complete g⁵ → g⁶ step formalization

**Labels:** `lean`, `formal-verification`, `large-cardinals`, `hyper-mahlo`, `volume-IV`

---

### Summary

`lean/Main.lean` proves that the regeneration hierarchy is unbounded (`regeneration_unbounded`) and that ordinal regeneration levels satisfy the Mahlo-like stationary property (`regeneration_hierarchy_mahlo`). However, the **specific claim** from `README.md` — that g⁵/g⁶ levels are *hyper-Mahlo* (not merely Mahlo) — needs to be formalized explicitly.

---

### Background

From `README.md`:
> - Lean-verified proofs for scaling hierarchies (**g⁵/g⁶ → hyper-Mahlo regenerations**)

From `lean/Main.lean` (Part E comment):
> *Volume IV master theorem: for regular uncountable α, ordinalNextLevel produces Mahlo-like levels.*

The current proof establishes:
- `IsMahloLike`: closure points are stationary (1-Mahlo analog)
- `regeneration_hierarchy_mahlo`: the next ordinal regeneration level is Mahlo-like

**Hyper-Mahlo** requires:
- A cardinal α is 1-Mahlo if the set of Mahlo cardinals below α is stationary
- α is 2-Mahlo if the set of 1-Mahlo cardinals below α is stationary
- α is hyper-Mahlo (ω-Mahlo) if this holds at every finite level

The `g⁶ = 33` connection in the crystal model suggests the framework should accommodate at least 6 iterated Mahlo levels.

---

### Scope of this issue

- [ ] Define `IsMahloLike_n : ℕ → Ordinal → Prop` in Lean 4 (iterated Mahlo hierarchy)
  - `IsMahloLike_n 0 α` ↔ current `IsMahloLike α`
  - `IsMahloLike_n (k+1) α` ↔ `{β < α | IsMahloLike_n k β}` is stationary below α
- [ ] Prove `mahlo_iter_unbounded : ∀ n k : ℕ, ∃ α, IsMahloLike_n n α` (existence of n-Mahlo cardinals for each n, assuming large cardinal axioms)
- [ ] Connect to `g6Level`: state a theorem that `g6Level.level = 6` implies the relevant iterated regeneration satisfies `IsMahloLike_n 6`
- [ ] Note explicitly which steps require `sorry` or large cardinal axioms beyond ZFC, and mark them accordingly

---

### Acceptance criteria

1. `IsMahloLike_n` is defined and compiles.
2. The base case (`n = 0`) is provably equivalent to `IsMahloLike`.
3. `g6_mahlo_level` (or similar) is stated as a theorem connecting `g6Level` to the hierarchy.
4. Any use of `sorry` or large cardinal axioms is explicitly documented.
5. `lake build` passes.

---

### References

- `lean/Main.lean` — `IsMahloLike`, `closurePoints_stationary`, Part D/E
- `README.md` — g⁵/g⁶ hyper-Mahlo claim
- `docs/index.md` — g⁶ crystal: 33 layers, `g⁶ · τ = 66`
- Kanamori, *The Higher Infinite*, Springer — iterated Mahlo hierarchy definition
- Mathlib4 `SetTheory.Ordinal.Basic`
