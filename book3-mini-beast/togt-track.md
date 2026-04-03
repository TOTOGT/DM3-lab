# TOGT Track — Kernel, Templates, and Example Vertent Embeddings

**Status:** Edited Web Edition artifact (DM3-Lab).  
**Purpose:** Define the minimal TOGT kernel (typed HOL + operator calculus) and provide D1/D2 templates and worked vertent embeddings. This file is designed to be used by students, LLM agents, and maintainers as the canonical "language layer" for Living Book 3.

> Note on sources: This file intentionally avoids verbatim excerpts from PDFs unless explicitly marked as Locked Excerpt and traceable to pasted source text in the repo workflow.

---

## 0) One-paragraph thesis (canonical)

**TOGT** is a typed higher-order logic and operator-first meta-language for embedding and connecting explanatory approaches ("vertents") across domains and scales. TOGT does not attempt to declare vertents wrong. Instead, it provides a translation discipline: map primitives → operators → invariants → bridge statements → certificates. The canonical TOGT sentence form is:
\[
G = U \circ F \circ K \circ C.
\]

---

## 1) Normative rule: Vertent Respect Principle (VRP)

**VRP:** Do not refute a vertent by rhetoric. Embed it.

For any vertent \(M\):
1) Identify its primitives: \(X\) (states), \(O\) (observables), \(D\) (data).  
2) Identify operators: what transforms states/observables?  
3) Identify invariants/constraints: what is conserved or assumed?  
4) Identify compression: what the vertent ignores/approximates.  
5) Propose **bridge statements** to other vertents: when is one a limit, coarse-graining, or special case of the other?  
6) Produce **certificates**: finite artifacts that test bridge statements empirically (or formally, when possible).

Disagreement between vertents is handled by **empirical discriminators** (bridge tests), not dismissal.

---

## 2) Minimal TOGT kernel (machine-usable)

### 2.1 Core types
- **X** — state space (discrete set, manifold, or hybrid)  
- **O** — observables (measured/derived quantities)  
- **D** — data streams (samples, time series, images, logs)  
- **M** — model class / vertent (named explanatory approach)  
- **K** — constraints / priors / invariants (axioms, conserved quantities)

### 2.2 Canonical operators (sentence form)
- **C (Capture / Compression):** world/state → data/representation (encoding, measurement, coarse-graining)  
- **K (Constraint / Curvature):** valuation/constraint operator (thresholds, invariants, regularizers; includes \(K^*\))  
- **F (Flux / Folding):** dynamics operator (flow; at threshold can produce folding/non-injectivity)  
- **U (Update / Unify):** learning/unfolding/selection operator (fit, merge, choose stable branch)  
- **Sentence:** \(G = U \circ F \circ K \circ C\)

### 2.3 Bridges (typed comparators)
A **bridge** is a typed statement that makes two vertents comparable:
- **Bridge(name):** `(types, measures) ⊢ inequality/equivalence ⇒ testable certificate recipe`

Examples (schematic):
- Drift bridge: \(\mathbb{E}[\Delta V] < 0\) under a measure induced by \(C,K\)  
- Curvature bridge: threshold crossing \(K(x)\ge K^*\) implies fold signatures in \(F\)  
- Spectral bridge: transfer operator spectra correlate with empirical mixing rates

### 2.4 Certificates (finite empirical anchors)
A **certificate** is a finite artifact bundle \((\mathcal{T},\mathcal{M},\mathcal{D},\mathcal{R})\):
- \(\mathcal{T}\): table/matrix/plot with explicit schema  
- \(\mathcal{M}\): minimal model spec (operator chain + parameters)  
- \(\mathcal{D}\): dataset slice (query + window + preprocessing)  
- \(\mathcal{R}\): decision rule (pass/fail, CI bounds, thresholds)

Certificates MUST include reproducible generation steps (script or pseudocode).

---

## 3) D1 / D2 outputs (templates)

### 3.1 D1 — Translation Skeleton (CEFR A2 → TOGT D1)
**Goal:** Minimal embedding: identify types + operators + one certificate placeholder.

```json
{
  "vertent_name": "string",
  "domain": "biology|physics|finance|other",
  "scale": "string (e.g., 'cellular', 'magnetotail', 'tick')",
  "X": "state space (plain description)",
  "O": ["observable1", "observable2"],
  "D": "data source description",
  "operators": {
    "C": "one-line capture/compression",
    "K": "one-line constraint/curvature",
    "F": "one-line dynamics/folding",
    "U": "one-line update/unify"
  },
  "bridge_candidate": "one-line inequality/equivalence (optional)",
  "certificate_placeholder": {
    "name": "string",
    "schema": ["col:type", "col:type"],
    "decision_rule": "string"
  }
}
```

**D1 writing rule:** 2 short seed sentences + the operator chain + one measurable bridge candidate.

### 3.2 D2 — Research Form (CEFR B2/C1 → TOGT D2)
**Goal:** Reproducible bridge test plan + certificate spec.

```json
{
  "vertent_name": "string",
  "domain": "string",
  "X": "formal/typed state description",
  "O": ["observables"],
  "D": {
    "source": "string",
    "query": "string",
    "window": "ISO range",
    "preprocessing": ["steps"]
  },
  "operator_chain": {
    "C": {"type": "map", "params": {}},
    "K": {"type": "map", "params": {}},
    "F": {"type": "map", "params": {}},
    "U": {"type": "map", "params": {}}
  },
  "bridge_statements": [
    {
      "latex": "string",
      "null_hypothesis": "string",
      "alt_hypothesis": "string",
      "estimator": "string",
      "uncertainty": "bootstrap|bayes|asymptotic"
    }
  ],
  "certificates": [
    {
      "name": "string",
      "schema": ["col:type"],
      "generation": "pseudocode or command",
      "decision_rule": "pass/fail rule"
    }
  ],
  "repro_notes": ["hardware", "random_seed_policy", "versioning"]
}
```

---

## 4) Worked example vertent embeddings (D2-style)

### 4.1 Biology: Neural oscillations and coherence (example)
- **X:** phase–amplitude trajectories \(\Phi(t)\in \mathbb{S}^1\times\mathbb{R}_{\ge0}\)  
- **O:** band power, phase-locking index (PLI), cross-frequency coupling  
- **C:** bandpass + Hilbert (phase/amplitude extraction)  
- **K:** curvature/coherence functional over embeddings (windowed)  
- **F:** local coupling dynamics on phases  
- **U:** update of global coherence measure (learning/selection)

**Bridge candidate (example):** \(\mathbb{E}[\Delta V] < 0\) under a windowed coherence-induced measure.

**Certificate schema:** `neural_coherence_drift.csv`  
- `window_start:time, window_end:time, drift:float, stderr:float, n:int`

---

## 5) Next formalization steps (action plan)
1) Define a minimal TOGT macro set for KaTeX in the Living Book.  
2) Create "Bridge + Certificate" checklists for each chapter.  
3) Add computational supplement conventions: CSV schemas, JSON summaries, seeds, versioning.  
4) (Optional) Begin a Lean 4/AXLE track: formalize typed operators + basic lemmas for discrete maps.

---

## 6) Integration instructions (for Living Book HTML)
- Every major section in `index.html` should include: CEFR seed sentences (A2/B2), TOGT D1 skeleton (JSON snippet), TOGT D2 research form (JSON snippet), Bridge statement(s) + Certificate schema(s).  
- Add a page toggle: "TOGT view" (shows TOGT blocks by default).
