#!/usr/bin/env python3
"""
scripts/collatz_c9_2_fourier_v2.py

Pure-stdlib Fourier diagnostics for Collatz C9.2 (Option 1).

Input:
  - CSV produced by scripts/collatz_c9_2_sampling_option1.py
    Expected columns:
      residue_a, hat_p
    (Other columns may exist; ignored.)

Output files (in --out-dir):
  - c9_2_M{M}_N{N}_fourier.json
  - c9_2_M{M}_N{N}_fourier_modes.csv

DFT convention:
  Let q = 2^M. Define mean_hat_p as the mean of hat_p(a) over residues a for which
  hat_p is defined (non-empty in CSV).
  Define g[a] = (hat_p(a) - mean_hat_p) for defined residues, and g[a] = 0 for
  undefined residues.  (Policy A: undefined treated as "not present".)
  Compute the length-q DFT:
      F[xi] = (1/q) * sum_{a=0}^{q-1} g[a] * exp(-2pi i xi a / q)

FFT:
  Uses a radix-2 Cooley-Tukey FFT (O(q log q)) implemented in stdlib.

Diagnostics produced:
  - per-v2 buckets of |F(xi)| for xi != 0:
      bucket r contains xi with v2(xi)=r (clamped to M-1 for safety)
      stats: count, max_absF, rms_absF
  - rms_ratio per bucket r:
      rms_absF(r) / rms_absF(0)   (for r>=1, if rms_absF(0)>0)
    and avg_rms_ratio across r=1..M-1
  - l2_variance_empirical:
      mean over defined residues of (hat_p - mean_hat_p)^2
  - sparse_fraction_hatp:
      fraction over defined residues with |hat_p - 0.5| >= threshold (default 0.05)

CLI:
  python3 scripts/collatz_c9_2_fourier_v2.py --input scripts/out/c9_2_M12_N100000.csv --out-dir scripts/out

Notes:
  - Do NOT commit produced JSON/CSV; attach artifacts to issues as requested.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import re
from typing import List, Tuple


TAU = 2.0 * math.pi


def v2_int(x: int) -> int:
    if x == 0:
        return 10**9
    v = 0
    while (x & 1) == 0:
        x >>= 1
        v += 1
    return v


def parse_M_N_from_filename(path: str) -> Tuple[int, int]:
    base = os.path.basename(path)
    m = re.search(r"_M(\d+)_N(\d+)\.csv$", base)
    if not m:
        raise ValueError(f"Could not parse M,N from filename: {base} (expected ..._M{{M}}_N{{N}}.csv)")
    return int(m.group(1)), int(m.group(2))


def fft_inplace(a: List[complex]) -> None:
    """
    In-place radix-2 FFT (forward transform), no normalization.
    a length must be power of 2.
    """
    n = len(a)
    if n == 0 or (n & (n - 1)) != 0:
        raise ValueError("fft_inplace requires length power of 2")

    # Bit-reversal permutation
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            a[i], a[j] = a[j], a[i]

    # Cooley-Tukey
    length = 2
    while length <= n:
        ang = -TAU / length
        wlen = complex(math.cos(ang), math.sin(ang))
        for i in range(0, n, length):
            w = 1.0 + 0.0j
            half = length // 2
            for j in range(i, i + half):
                u = a[j]
                v = a[j + half] * w
                a[j] = u + v
                a[j + half] = u - v
                w *= wlen
        length <<= 1


def load_hat_p(input_csv: str, q: int) -> Tuple[List[float], List[bool], int]:
    """
    Returns:
      hat_p: length-q float array (0 for undefined residues)
      defined: length-q bool array
      n_defined: number of defined residues
    """
    hat_p = [0.0] * q
    defined = [False] * q
    n_defined = 0

    with open(input_csv, newline="") as f:
        r = csv.DictReader(f)
        for row in r:
            if "residue_a" not in row:
                continue
            a_str = row.get("residue_a", "")
            if a_str is None or a_str == "":
                continue
            try:
                a = int(a_str)
            except Exception:
                continue
            if a < 0 or a >= q:
                continue

            hp_str = row.get("hat_p", "")
            if hp_str is None:
                continue
            hp_str = hp_str.strip()
            if hp_str == "" or hp_str.lower() == "none":
                continue

            try:
                hp = float(hp_str)
            except Exception:
                continue

            if not defined[a]:
                n_defined += 1
            defined[a] = True
            hat_p[a] = hp

    return hat_p, defined, n_defined


def compute_mean_and_l2(hat_p: List[float], defined: List[bool], n_defined: int) -> Tuple[float, float]:
    if n_defined <= 0:
        return float("nan"), float("nan")

    s = 0.0
    for a, ok in enumerate(defined):
        if ok:
            s += hat_p[a]
    mean_hat_p = s / n_defined

    var = 0.0
    for a, ok in enumerate(defined):
        if ok:
            d = hat_p[a] - mean_hat_p
            var += d * d
    l2_var = var / n_defined
    return mean_hat_p, l2_var


def compute_sparse_fraction_hatp(hat_p: List[float], defined: List[bool], n_defined: int, threshold: float) -> Tuple[float, int, int]:
    if n_defined <= 0:
        return float("nan"), 0, 0
    bad = 0
    for a, ok in enumerate(defined):
        if ok and abs(hat_p[a] - 0.5) >= threshold:
            bad += 1
    return bad / n_defined, bad, n_defined


def main() -> int:
    ap = argparse.ArgumentParser(description="C9.2 Fourier diagnostics (stdlib-only, FFT-based)")
    ap.add_argument("--input", required=True, help="Input sampler CSV: c9_2_M{M}_N{N}.csv")
    ap.add_argument("--out-dir", default="scripts/out", help="Output directory")
    ap.add_argument("--top-k", type=int, default=50, help="Top modes (by |F|) to include in JSON summary")
    ap.add_argument("--threshold", type=float, default=0.05, help="Sparse threshold for |hat_p-0.5|")
    args = ap.parse_args()

    M, N = parse_M_N_from_filename(args.input)
    q = 1 << M

    os.makedirs(args.out_dir, exist_ok=True)

    hat_p, defined, n_defined = load_hat_p(args.input, q=q)
    mean_hat_p, l2_var = compute_mean_and_l2(hat_p, defined, n_defined)
    sparse_frac, sparse_bad, sparse_total = compute_sparse_fraction_hatp(hat_p, defined, n_defined, args.threshold)

    # Build g[a] as complex array for FFT
    g = [0.0 + 0.0j] * q
    if n_defined > 0 and not math.isnan(mean_hat_p):
        for a in range(q):
            if defined[a]:
                g[a] = complex(hat_p[a] - mean_hat_p, 0.0)
            else:
                g[a] = 0.0 + 0.0j

    # FFT forward; then scale by 1/q to match F definition
    fft_inplace(g)
    inv_q = 1.0 / q
    F = [z * inv_q for z in g]  # F[xi]

    # Per-v2 buckets over xi != 0
    buckets = {r: [] for r in range(M)}
    for xi in range(1, q):
        r = v2_int(xi)
        if r > M - 1:
            r = M - 1
        buckets[r].append(abs(F[xi]))

    per_v2_bucket = {}
    rms0 = 0.0
    for r in range(M):
        arr = buckets.get(r, [])
        if not arr:
            per_v2_bucket[r] = {"count": 0, "max_absF": 0.0, "rms_absF": 0.0, "rms_ratio": None}
            continue
        mx = max(arr)
        rms = math.sqrt(sum(x * x for x in arr) / len(arr))
        per_v2_bucket[r] = {"count": len(arr), "max_absF": mx, "rms_absF": rms, "rms_ratio": None}
        if r == 0:
            rms0 = rms

    # RMS ratios vs r=0 bucket
    rms_ratios = []
    if rms0 > 0:
        for r in range(1, M):
            rms_r = per_v2_bucket[r]["rms_absF"]
            ratio = (rms_r / rms0) if rms_r is not None else None
            per_v2_bucket[r]["rms_ratio"] = ratio
            if ratio is not None:
                rms_ratios.append(ratio)

    avg_rms_ratio = (sum(rms_ratios) / len(rms_ratios)) if rms_ratios else None

    # Modes list (xi != 0), sorted by |F|
    modes = []
    for xi in range(1, q):
        z = F[xi]
        modes.append(
            {
                "xi": xi,
                "v2_xi": min(v2_int(xi), M - 1),
                "absF": float(abs(z)),
                "reF": float(z.real),
                "imF": float(z.imag),
            }
        )
    modes.sort(key=lambda m: m["absF"], reverse=True)

    top_modes = modes[: max(0, args.top_k)]

    # Write full modes CSV (all xi != 0)
    base = os.path.basename(args.input).replace(".csv", "")
    out_modes_csv = os.path.join(args.out_dir, f"{base}_fourier_modes.csv")
    with open(out_modes_csv, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["xi", "v2_xi", "absF", "reF", "imF"])
        for xi in range(1, q):
            z = F[xi]
            w.writerow([xi, min(v2_int(xi), M - 1), abs(z), z.real, z.imag])

    # Write JSON summary
    out_json = os.path.join(args.out_dir, f"{base}_fourier.json")
    summary = {
        "input_csv": args.input,
        "observable_policy": {
            "option": "Option 1",
            "event_A": "n odd",
            "event_B": "T(n) < n, with T(n)=(3n+1)/2^{v2(3n+1)} on odd n",
            "undefined_residue_policy": "Policy A: undefined hat_p treated as not present; g[a]=0 for undefined residues",
        },
        "M": M,
        "N": N,
        "q": q,
        "n_defined_hat_p": n_defined,
        "mean_hat_p": mean_hat_p,
        "l2_variance_empirical": l2_var,
        "sparse_threshold": args.threshold,
        "sparse_fraction_hatp": sparse_frac,
        "sparse_bad": sparse_bad,
        "sparse_total": sparse_total,
        "per_v2_bucket": per_v2_bucket,
        "avg_rms_ratio": avg_rms_ratio,
        "top_modes": top_modes,
        "notes": "Use avg_rms_ratio for SDH verdict per project rules. Modes are additive characters on Z/2^MZ.",
    }
    with open(out_json, "w") as f:
        json.dump(summary, f, indent=2)

    print(f"Wrote: {out_json}")
    print(f"Wrote: {out_modes_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
