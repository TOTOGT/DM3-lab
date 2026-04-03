#!/usr/bin/env python3
"""
C9.2 Sampling Script — Collatz consecutive (1,1) decorrelation study.

For each sampled odd integer n ≥ 33 computes:
  v1     = v2(3n+1)            2-adic valuation of first Collatz step
  n'     = (3n+1) / 2^v1       next odd integer in orbit
  v2_nxt = v2(3n'+1)           2-adic valuation of second step

Records the (1,1)-event: v1==1 AND v2_nxt==1, weighted by w(n)=1/log(n).
Aggregates hat_p per dyadic residue class r = n mod 2^M.

Outputs
-------
  <out>/c9_2_M{M}_N{N}.csv              per-class statistics
  <out>/c9_2_summary_M{M}_N{N}.json     summary metrics + verdict
  <out>/c9_2_M{M}_N{N}_hatp_vs_residue.png
  <out>/c9_2_M{M}_N{N}_v2_rms.png

G6 LLC · Pablo Nogueira Grossi · Newark NJ · 2026
MIT License
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import time
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


# ── helpers ──────────────────────────────────────────────────────────────────

def v2_vec(arr: np.ndarray) -> np.ndarray:
    """Element-wise 2-adic valuation for a positive int64 array."""
    arr = arr.astype(np.int64)
    lowest_bit = arr & (-arr)                          # isolate lowest set bit
    return np.floor(np.log2(lowest_bit.astype(np.float64))).astype(np.int32)


def sample_and_aggregate(
    N: int,
    M: int,
    seed: int = 42,
    max_n: int = 10**9,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Sample N odd integers in [33, max_n) and aggregate per residue class
    mod 2^M.

    Returns
    -------
    weight_sum : shape (2^M,)  total w(n) per class
    hit_weight : shape (2^M,)  weighted (1,1)-hits per class
    n_count    : shape (2^M,)  raw sample count per class
    """
    rng = np.random.default_rng(seed + M)
    mod = 1 << M

    # Draw raw integers in [33, max_n); force odd
    batch = rng.integers(33, max_n, size=N * 2, dtype=np.int64)
    batch = np.where(batch % 2 == 0, batch + 1, batch)
    batch = batch[:N]

    # First macro-step: 3n+1, then divide by 2^v1
    m1   = 3 * batch + 1                               # int64, always even
    v1   = v2_vec(m1)                                  # shape (N,)
    n1   = np.right_shift(m1, v1)                      # next odd, shape (N,)

    # Second macro-step
    m2      = 3 * n1 + 1
    v2_next = v2_vec(m2)

    hits    = ((v1 == 1) & (v2_next == 1)).astype(np.float64)
    weights = 1.0 / np.log(batch.astype(np.float64))

    residues = batch & (mod - 1)                       # n mod 2^M, always odd

    weight_sum = np.bincount(residues, weights=weights,          minlength=mod)
    hit_weight = np.bincount(residues, weights=weights * hits,   minlength=mod)
    n_count    = np.bincount(residues, minlength=mod)

    return weight_sum, hit_weight, n_count


def v2_of_class(r: int) -> int:
    """2-adic valuation of (3r+1) for odd residue r."""
    val = int(3 * r + 1)
    if val == 0:
        return 99
    count = 0
    while val % 2 == 0:
        val //= 2
        count += 1
    return count


# ── main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="C9.2 sampling: Collatz consecutive (1,1) decorrelation"
    )
    parser.add_argument("--N",           type=int,   default=100_000)
    parser.add_argument("--M",           type=int,   default=12)
    parser.add_argument("--window-type", default="dyadic", choices=["dyadic"])
    parser.add_argument("--output",      default="scripts/out")
    args = parser.parse_args()

    N, M = args.N, args.M
    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"[C9.2] N={N:,}  M={M}  window={args.window_type}")
    t0 = time.perf_counter()

    weight_sum, hit_weight, n_count = sample_and_aggregate(N, M)

    # Odd residue classes only (n is always odd → residue is always odd)
    mod          = 1 << M
    odd_residues = list(range(1, mod, 2))

    # hat_p per class (classes with no samples are excluded from stats)
    hat_p   = {}
    for r in odd_residues:
        if weight_sum[r] > 0:
            hat_p[r] = float(hit_weight[r] / weight_sum[r])

    if not hat_p:
        raise RuntimeError("No samples collected — check N and range.")

    # mean_hat_p (weight-sum weighted)
    total_w    = sum(weight_sum[r] for r in hat_p)
    mean_hat_p = sum(hat_p[r] * weight_sum[r] for r in hat_p) / total_w

    # residuals
    residuals = {r: hat_p[r] - mean_hat_p for r in hat_p}

    # L2_variance (weight-sum weighted mean of squared residuals)
    L2_variance = sum(residuals[r] ** 2 * weight_sum[r] for r in hat_p) / total_w
    overall_rms = math.sqrt(L2_variance)

    # v2 class label for each residue
    v2_class = {r: v2_of_class(r) for r in hat_p}

    # Per-v2 RMS
    v2_groups: dict[int, list[float]] = defaultdict(list)
    for r in hat_p:
        v2_groups[v2_class[r]].append(residuals[r])

    per_v2_rms: dict[int, float] = {
        v: float(np.sqrt(np.mean(np.array(rs) ** 2)))
        for v, rs in v2_groups.items()
    }

    rms_ratios: dict[int, float] = {
        v: (per_v2_rms[v] / overall_rms if overall_rms > 0 else 0.0)
        for v in per_v2_rms
    }
    avg_rms_ratio = float(np.mean(list(rms_ratios.values()))) if rms_ratios else 0.0

    # Sparse fraction (classes with < 5 raw samples)
    n_total_classes  = len(odd_residues)
    sparse_fraction  = sum(1 for r in odd_residues if n_count[r] < 5) / n_total_classes

    runtime = time.perf_counter() - t0

    # Verdict
    if avg_rms_ratio <= 0.7:
        verdict = "Strong SDH"
    elif avg_rms_ratio <= 0.9:
        verdict = "Suggestive SDH"
    else:
        verdict = "Weak SDH"

    l2_flag     = L2_variance   >= 0.05
    sparse_flag = sparse_fraction >= 0.05

    # ── CSV ──────────────────────────────────────────────────────────────────
    csv_path = out_dir / f"c9_2_M{M}_N{N}.csv"
    with open(csv_path, "w", newline="") as fh:
        writer = csv.DictWriter(
            fh,
            fieldnames=["residue","hat_p","residual","v2",
                        "weight_sum","hit_weight","n_samples"],
        )
        writer.writeheader()
        for r in sorted(hat_p):
            writer.writerow({
                "residue":    r,
                "hat_p":      f"{hat_p[r]:.8f}",
                "residual":   f"{residuals[r]:.8f}",
                "v2":         v2_class[r],
                "weight_sum": f"{float(weight_sum[r]):.6f}",
                "hit_weight": f"{float(hit_weight[r]):.6f}",
                "n_samples":  int(n_count[r]),
            })
    print(f"  CSV:  {csv_path}")

    # ── Summary JSON ─────────────────────────────────────────────────────────
    summary = {
        "M":                   M,
        "N":                   N,
        "window_type":         args.window_type,
        "n_residue_classes":   n_total_classes,
        "n_sampled_classes":   len(hat_p),
        "mean_hat_p":          round(mean_hat_p,    8),
        "L2_variance":         round(L2_variance,   8),
        "overall_rms":         round(overall_rms,   8),
        "per_v2_rms":          {str(k): round(v, 8) for k, v in sorted(per_v2_rms.items())},
        "rms_ratios":          {str(k): round(v, 8) for k, v in sorted(rms_ratios.items())},
        "avg_rms_ratio":       round(avg_rms_ratio, 8),
        "sparse_fraction":     round(sparse_fraction, 8),
        "l2_failure_flag":     bool(l2_flag),
        "sparse_failure_flag": bool(sparse_flag),
        "verdict":             verdict,
        "runtime_seconds":     round(runtime, 3),
    }
    json_path = out_dir / f"c9_2_summary_M{M}_N{N}.json"
    with open(json_path, "w") as fh:
        json.dump(summary, fh, indent=2)
    print(f"  JSON: {json_path}")

    # ── Plot 1: hat_p vs residue ──────────────────────────────────────────────
    sorted_rs = sorted(hat_p)
    xs     = np.array(sorted_rs, dtype=np.float64)
    ys     = np.array([hat_p[r] for r in sorted_rs])
    colors = np.array([v2_class[r] for r in sorted_rs])

    fig, ax = plt.subplots(figsize=(10, 4))
    sc = ax.scatter(xs, ys, c=colors, s=2, cmap="viridis", alpha=0.7)
    ax.axhline(mean_hat_p, color="red", lw=1.5, ls="--",
               label=f"mean = {mean_hat_p:.4f}")
    plt.colorbar(sc, ax=ax, label="v₂ class")
    ax.set_xlabel("Residue r = n mod 2^M")
    ax.set_ylabel("hat_p(r)")
    ax.set_title(f"C9.2  hat_p vs residue  |  M={M}  N={N:,}")
    ax.legend(fontsize=8)
    png1 = out_dir / f"c9_2_M{M}_N{N}_hatp_vs_residue.png"
    fig.tight_layout()
    fig.savefig(png1, dpi=120)
    plt.close(fig)
    print(f"  Plot: {png1}")

    # ── Plot 2: v2 vs per-v2 RMS (log scale) ─────────────────────────────────
    vs       = sorted(per_v2_rms)
    rms_vals = [per_v2_rms[v] for v in vs]

    fig, ax = plt.subplots(figsize=(7, 4))
    ax.semilogy(vs, rms_vals, "o-", color="steelblue", lw=1.5)
    ax.axhline(overall_rms, color="red", lw=1, ls="--",
               label=f"overall RMS = {overall_rms:.4f}")
    ax.set_xlabel("v₂ bucket")
    ax.set_ylabel("RMS of residuals (log scale)")
    ax.set_title(f"C9.2  per-v₂ RMS  |  M={M}  N={N:,}")
    ax.legend(fontsize=8)
    ax.grid(True, which="both", alpha=0.4)
    png2 = out_dir / f"c9_2_M{M}_N{N}_v2_rms.png"
    fig.tight_layout()
    fig.savefig(png2, dpi=120)
    plt.close(fig)
    print(f"  Plot: {png2}")

    # ── Console summary ───────────────────────────────────────────────────────
    print(f"  mean_hat_p    = {mean_hat_p:.6f}")
    print(f"  L2_variance   = {L2_variance:.6f}"
          + ("  [L2 FLAG]"     if l2_flag     else ""))
    print(f"  overall_rms   = {overall_rms:.6f}")
    print(f"  avg_rms_ratio = {avg_rms_ratio:.6f}")
    print(f"  sparse_frac   = {sparse_fraction:.6f}"
          + ("  [SPARSE FLAG]" if sparse_flag  else ""))
    print(f"  Verdict       : {verdict}")
    print(f"  Runtime       : {runtime:.2f}s")


if __name__ == "__main__":
    main()
