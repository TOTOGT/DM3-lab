# C9.2 — Monte-Carlo & Finite-Range Checks for Consecutive (1,1) Probabilities

**Goal:** Produce robust numerical evidence for the *decorrelation hypothesis*
under the contact-form weight `w(n) ≈ 1/log n`.

---

## Background

For an odd integer `n` we define the **half-step Collatz map**

```
T(n) = (3n + 1) / 2       (n odd)
```

The **"11 event"** is: `n` is odd **and** `T(n)` is odd.
`T(n)` is odd if and only if `n ≡ 3 (mod 4)`, so under the **uniform** measure
on odd integers the unconditional probability is exactly

```
p11_uniform = 1/2
```

The **contact-form weight** is

```
w(n) = 1 / log(n)
```

The **decorrelation hypothesis** asserts that, under this weight, the parity
bits at different orbit positions are asymptotically independent.  Concretely,
the weighted

```
p11 = Σ_{n odd, start≤n≤end} w(n) · 1[T(n) is odd]
    / Σ_{n odd, start≤n≤end} w(n)
```

should converge to `1/2` as the window grows, and the **auto-correlation
function** (ACF) of the parity orbit should decay toward zero.

---

## Scripts

| Script | Purpose |
|---|---|
| `collatz_c9_2_sampling.py` | Monte-Carlo sampler — outputs CSV and JSON |
| `collatz_c9_2_plots.py` | Reads JSON summaries — outputs PNG plots |

### `collatz_c9_2_sampling.py`

```
python scripts/collatz_c9_2_sampling.py [options]

Options:
  --start INT   Lower window bound (rounded up to odd ≥ 33).  Default: 33
  --end   INT   Upper window bound.                            Default: 100 000
  --M     INT   Number of Monte-Carlo draws.                   Default: 100 000
  --depth INT   Length of full-Collatz parity orbit per draw.  Default: 20
  --seed  INT   RNG seed (omit for non-reproducible run).
  --output DIR  Output directory.                              Default: scripts/out
```

**Outputs** (inside `--output`):

| File | Content |
|---|---|
| `c9_2_start<s>_end<e>_M<m>.csv` | Raw draws: columns `n, w, b1_half, b0…b{depth-1}` |
| `c9_2_start<s>_end<e>_M<m>_summary.json` | Aggregate stats: `p11`, `p_k`, `acf`, `convergence` |

### `collatz_c9_2_plots.py`

```
python scripts/collatz_c9_2_plots.py \
    --summary scripts/out/<summary1>.json [<summary2>.json …] \
    --output  scripts/out
```

**Outputs** (inside `--output`):

| File | Content |
|---|---|
| `convergence_<tag>.png` | p₁₁ vs. sample count |
| `acf_<tag>.png` | Parity-orbit auto-correlation C(lag) with 95 % CI band |
| `marginals_<tag>.png` | Marginal P(b_k=1) for each orbit position |
| `multi_window_convergence.png` | Overlay of all supplied experiments |

---

## Reproducing the Full Experiment

```bash
# Install dependencies (once)
pip install numpy matplotlib

# Window 1 — 10^5 draws over [33, 10^5]
python scripts/collatz_c9_2_sampling.py \
    --start 33 --end 100000 --M 100000 --depth 20 --seed 42 \
    --output scripts/out

# Window 2 — 10^6 draws over [33, 10^6]
python scripts/collatz_c9_2_sampling.py \
    --start 33 --end 1000000 --M 1000000 --depth 20 --seed 42 \
    --output scripts/out

# Generate all plots (including multi-window comparison)
python scripts/collatz_c9_2_plots.py \
    --summary \
        scripts/out/c9_2_start33_end100000_M100000_summary.json \
        scripts/out/c9_2_start33_end1000000_M1000000_summary.json \
    --output scripts/out
```

---

## What the Outputs Show

### Convergence plot (`convergence_*.png`)

Tracks the running weighted `p11` as more draws are collected.
**Expected behavior:** rapid initial fluctuation followed by convergence to
a value near `0.5`.  Slow convergence or a persistent offset would suggest
a non-trivial effect of the contact-form weight.

### ACF plot (`acf_*.png`)

Auto-correlation `C(lag)` of the parity orbit `b_0, b_1, …`.  The crimson
dashed lines mark the `±1.96/√M` 95 % confidence band under the i.i.d.
null hypothesis.
**Expected behavior under decorrelation:** all bars should lie inside the
band for `lag ≥ 2` (lag 1 is structurally zero for odd starting points
because odd → always even under the standard Collatz map).

### Marginals plot (`marginals_*.png`)

Weighted probability that orbit position `k` is odd.  Under the i.i.d.
hypothesis every bar should be near `0.5`.

---

## Methodology and Limitations

* **Sampling:** odd integers are drawn *uniformly at random* from `[start, end]`
  and then re-weighted by `w(n) = 1/log(n)`.  This is importance-sampling
  consistent with the contact-form measure.
* **Finite window bias:** for small windows the log-weight introduces a mild
  preference for smaller `n`; this bias shrinks as `end → ∞`.
* **No proof:** these scripts produce *numerical evidence* only.  They cannot
  prove the decorrelation hypothesis; they can only fail to find evidence
  against it.
* **Reproducibility:** supply `--seed` for fully reproducible runs.  All
  output filenames encode the window and draw count.

---

## Raw Data

Raw CSV files are **not** committed to this repository (they can be several
hundred MB for `M = 10^6`).  Attach them to the C9.2 issue or store them in a
shared drive.  The JSON summaries are small and safe to commit.
