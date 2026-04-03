## ZFC axiomatization: formal translation of dm³ axioms 1–8 into ZFC set theory

**Labels:** `lean`, `foundations`, `zfc`, `dm3`, `research`

---

### Summary

`README2.md` lists the epistemic status of TOGT claims and notes that a **ZFC translation** of the dm³ axioms is *proposed / philosophical* and not yet complete. This issue tracks the work of writing down dm³ Axioms 1–8 explicitly and translating them into ZFC (with or without large cardinal extensions).

---

### Background

From `README2.md`:
> **Conjectured / open:** Structural Hypothesis SH; Collatz Axioms 7–8; **ZFC translation**  
> **Proposed / philosophical:** GUT-level unification; Templar/mythic instantiations; string theory mapping

The `lean/Main.lean` file formalizes several results but the underlying axioms of the dm³ framework are not stated as a numbered list anywhere in the repository. Before Lean proofs can be complete, the axioms must be written down.

The `mappings/domain_mappings.md` states:
> *Three falsifiable predictions (allostatic unification law, circadian re-entrainment law, hormetic accumulation law) derive from the canonical triple (T*, μ_max, τ) = (2π, -2, 2).*

These predictions implicitly assume Axioms 1–8 — but the axioms themselves are not listed.

---

### Scope of this issue

**Part 1 — Write the axiom list:**
- [ ] Add `docs/dm3_axioms.md`: a numbered list of dm³ Axioms 1–8 in precise mathematical language (not Lean yet, just English + symbols)
- [ ] For each axiom, note: (a) epistemic status, (b) which Lean theorems depend on it, (c) whether it is provable from ZFC or requires extra axioms

**Part 2 — ZFC translation:**
- [ ] For Axioms 1–6 (believed to follow from ZFC + definitions): write the ZFC statement in first-order logic
- [ ] For Axioms 7–8 (equivalent to open conjectures): note this explicitly

**Part 3 — Lean skeleton:**
- [ ] Add `lean/Dm3Axioms.lean` with the axioms as `axiom` declarations or `def`s
- [ ] Mark which are theorems (can be proved) vs. genuine axioms (postulated)

---

### Acceptance criteria

1. `docs/dm3_axioms.md` lists all 8 axioms with their epistemic status.
2. The ZFC translation is present for at least Axioms 1–6.
3. `lean/Dm3Axioms.lean` compiles (`lake build`).
4. The document is honest about what is proved vs. assumed.

---

### References

- `README2.md` — epistemic status table
- `lean/Main.lean` — current Lean formalization
- `mappings/domain_mappings.md` — allostatic / circadian / hormetic laws
- Jech, *Set Theory*, Springer — ZFC reference
- Mathlib4 `Logic.Basic`
