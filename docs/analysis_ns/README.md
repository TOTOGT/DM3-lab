# NS Lane Analysis Notes

This directory holds **NS lane** analysis drafts, sketches, and LaTeX notes.

**NS (Non-Standard / Numerical-Spectral) lane** is a parallel research track to the D9 Collatz lane. It applies the dm³ operator framework to spectral and numerical analysis questions that are structurally analogous to the Collatz mixing hypothesis but arise in different mathematical settings.

---

## Filing Guidelines

- Keep NS notes **lane-pure**: do not reference Collatz deliverables or Collatz-specific filenames.
- Do not commit empirical CSV/JSON outputs — attach them to issues (N9.2 #8 / N9.1 #9) instead.
- Do not assume baseline `1/2` unless explicitly defined; record baseline `p0` in all summaries.
- Use clear filenames: `n9_v0.1_topic.tex`, `n9_v0.1_operator_estimate.tex`, etc.

---

## Current Status

Waiting for observable definition from issues N9.2 #8 / N9.1 #9:
- A/B event definitions
- Class space and scale parameter
- Admissibility conditions
- Windowing / weighting conventions
- Baseline `p0`

---

## Related Files

- `docs/c9_1_hypothesis.md` — Collatz lane analogue (H_mix statement and testing protocol)
- `docs/CONTRIBUTING_D9.md` — D9 contributor guide (useful as a structural template for NS contributions)
- `scripts/collatz_c9_2_sampling.py` — Sampling script (Collatz lane; adapt for NS observables)

