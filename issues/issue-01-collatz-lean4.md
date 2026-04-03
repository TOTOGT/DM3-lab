## AXLE Target 5 — Lean 4 formalization of the Collatz conjecture as a dm³-system

**Labels:** `lean`, `formal-verification`, `collatz`, `axle-target`, `help-wanted`

---

### Summary

The Collatz map `T(n) = n/2` (even) or `3n+1` (odd) has been proposed as a dm³-system with `{4→2→1}` as its unique attractor (see `README2.md` and `mappings/domain_mappings.md`). The structural framework is in place; what remains is formal verification in Lean 4.

The `lean/Main.lean` file already formalizes the core TOGT operator algebra and regeneration hierarchies. The next major target (AXLE Target 5) is extending this to the Collatz conjecture.

---

### Background

**Structural observation already noted in the docs:**
- Mean step ratio with `c = 3` gives `3/4 < 1` (mean contraction). ✓
- With `c = 5`: `5/4 > 1` (divergent). ✓
- `c = 3` is the minimal odd constant producing mean contraction. ✓

**What is NOT yet formalized (the open axioms):**

| Axiom | Statement | Status |
|---|---|---|
| Axiom 7 | No Collatz orbit diverges to +∞ | ❌ Open (equivalent to the conjecture) |
| Axiom 8 | `{4→2→1}` is the unique attractor | ❌ Open (equivalent to the conjecture) |

The Zenodo paper *"The Collatz Conjecture as a Canonical dm³-System"* explicitly does **not** claim a proof — it claims structural visibility prior to axiomatization. This issue tracks the Lean formalization of everything *except* the two open axioms, plus a framework that would make Axioms 7–8 clearly stated and checkable once a proof is found.

---

### Scope of this issue

- [ ] Add a `Collatz` namespace to `lean/Main.lean` (or a new file `lean/Collatz.lean`)
- [ ] Formalize the Collatz map `T : ℕ → ℕ` in Lean 4
- [ ] Prove the mean contraction lemma: `c = 3` gives mean step ratio `3/4 < 1`
- [ ] State `dm3CollatzSystem` as a `Dm3Triple` instance with the canonical invariants
- [ ] State Axiom 7 and Axiom 8 as `axiom` declarations (honest placeholders)
- [ ] Add a `-- TODO: Axiom 7 ↔ Collatz conjecture` comment linking to the conjecture
- [ ] All existing theorems in `Main.lean` must remain sorry-free

---

### Acceptance criteria

1. `lake build` passes with zero `sorry` in the Collatz section.
2. The two open axioms are clearly marked as `axiom` (not proved).
3. The mean contraction lemma is a theorem, not an axiom.
4. A doc-string explains the relationship between Axiom 7/8 and the conjecture.

---

### References

- `lean/Main.lean` — existing TOGT formalization
- `README2.md` — Collatz as dm³-system (priority domain section)
- Zenodo: *"The Collatz Conjecture as a Canonical dm³-System"* (DOI pending)
- Mathlib4: `Nat.even_or_odd`, `Nat.div_add_mod`
