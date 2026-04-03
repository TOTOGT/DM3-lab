"""
C9.2 Fourier analysis of per-residue mean log-drift (hat_p).

Reads the per-residue CSV produced by collatz_c9_2_sampling.py and computes
the discrete Fourier transform of the mean-centered hat_p function on Z/2^M Z.

Correctness notes
-----------------
- Mean computation: first-occurrence guard (`hat_p[a] is None` check prevents
  double-counting if the input CSV ever has duplicate residue rows).
- Sparsity baseline: mean-centered values — the baseline is the empirical
  residue mean, not a fixed constant such as 0.5.
- Observable metadata: `observable` field is set to "mean_log_drift".
- Policy A: residue classes that were never sampled contribute 0 to the FFT
  array after mean-centering (unseen hat_p → assigned the mean → delta = 0).
- Radix-2 FFT: q = 2^M is always a power of 2; an iterative Cooley-Tukey
  FFT avoids Python recursion-depth limits.

Outputs
-------
- JSON: summary statistics (mean_hat_p, l2_variance_empirical,
  sparse_fraction_hatp, avg_rms_ratio, per_v2_bucket)
- CSV: Fourier modes — one row per nonzero frequency (k, v2k, absF, ReF, ImF)

Usage
-----
    python scripts/collatz_c9_2_fourier.py --M 12 --N 100000 \\
        --input-dir scripts/out --output-dir scripts/out
"""

import argparse
import cmath
import csv
import json
import math
import os


# ---------------------------------------------------------------------------
# 2-adic valuation
# ---------------------------------------------------------------------------

def v2(n: int) -> int:
    """2-adic valuation: largest k such that 2^k divides n (0 if n == 0)."""
    if n == 0:
        return 0
    count = 0
    while n % 2 == 0:
        n >>= 1
        count += 1
    return count


# ---------------------------------------------------------------------------
# Iterative Cooley-Tukey radix-2 FFT
# ---------------------------------------------------------------------------

def fft(x):
    """
    In-place iterative Cooley-Tukey radix-2 FFT.

    Parameters
    ----------
    x : list[complex]
        Input; length *must* be a power of 2.

    Returns
    -------
    x : list[complex]
        DFT of the input (modified in place).
    """
    n = len(x)
    # Bit-reversal permutation
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            x[i], x[j] = x[j], x[i]

    # Butterfly stages
    length = 2
    while length <= n:
        ang = -2.0 * cmath.pi / length
        w_step = cmath.exp(complex(0, ang))
        for i in range(0, n, length):
            wn = complex(1, 0)
            half = length >> 1
            for k in range(half):
                u = x[i + k]
                v = x[i + k + half] * wn
                x[i + k] = u + v
                x[i + k + half] = u - v
                wn *= w_step
        length <<= 1

    return x


# ---------------------------------------------------------------------------
# CSV reader
# ---------------------------------------------------------------------------

def load_hat_p(csv_path: str) -> dict:
    """
    Read per-residue CSV and return {a: mean_log_drift}.

    The CSV must have a column named ``mean_log_drift`` or (for backward
    compatibility) ``hat_p``.  Only the *first* occurrence of each residue
    class is used; subsequent duplicates are silently skipped.
    """
    hat_p = {}
    with open(csv_path, newline='') as fh:
        reader = csv.DictReader(fh)
        # Determine which column name is present
        fieldnames = reader.fieldnames or []
        if 'mean_log_drift' in fieldnames:
            value_col = 'mean_log_drift'
        elif 'hat_p' in fieldnames:
            value_col = 'hat_p'
        else:
            raise ValueError(
                f"CSV {csv_path!r} has neither 'mean_log_drift' nor 'hat_p' column. "
                f"Found columns: {fieldnames}"
            )
        for row in reader:
            a = int(row['a'])
            if a not in hat_p:   # first-occurrence guard
                hat_p[a] = float(row[value_col])
    return hat_p


# ---------------------------------------------------------------------------
# Fourier analysis
# ---------------------------------------------------------------------------

def run_fourier(hat_p: dict, M: int):
    """
    Compute the DFT of the mean-centered hat_p signal on Z/q Z, q = 2^M.

    Parameters
    ----------
    hat_p : dict[int, float]
        Mapping from residue class a to mean log-drift.
    M : int
        Exponent; q = 2^M.

    Returns
    -------
    modes_rows : list[dict]
        One row per nonzero-magnitude frequency: {k, v2k, absF, ReF, ImF}.
    summary : dict
        Aggregate statistics.
    """
    q = 1 << M   # 2^M — always a power of 2

    # --- Mean computation (residue-weighted) ---
    # Only use the first occurrence of each residue (hat_p[a] is None guard
    # is already applied by load_hat_p; here we trust the dict is clean).
    seen = list(hat_p.keys())
    n_seen = len(seen)
    mean_hat_p = (
        sum(hat_p[a] for a in seen) / n_seen if n_seen > 0 else 0.0
    )

    # --- Build mean-centered array f of length q ---
    # Policy A: residues not present in hat_p contribute 0 after centering.
    # Seen residues: f[a] = hat_p[a] - mean_hat_p.
    # Unseen residues (even or not sampled): f[a] = 0.
    f = [complex(0, 0)] * q
    for a in seen:
        f[a] = complex(hat_p[a] - mean_hat_p, 0)

    # --- Radix-2 FFT (q = 2^M) ---
    F = fft(f)   # in-place; F is f after transform

    # --- Per-v2-bucket statistics (by v2 of the frequency index k) ---
    # DC component k=0: F[0] = sum(f) = 0 after mean-centering; skip.
    # For k in 1..q-1: v2(k) is clamped to M-1.
    per_v2_bucket_acc = {}   # bucket_key -> [sum_absF, sum_absF2, count]
    for k in range(1, q):
        v2k = min(v2(k), M - 1)
        bk = str(v2k)
        absF_k = abs(F[k])
        if bk in per_v2_bucket_acc:
            per_v2_bucket_acc[bk][0] += absF_k
            per_v2_bucket_acc[bk][1] += absF_k * absF_k
            per_v2_bucket_acc[bk][2] += 1
        else:
            per_v2_bucket_acc[bk] = [absF_k, absF_k * absF_k, 1]

    per_v2_bucket = {}
    for bk, (s, s2, cnt) in sorted(per_v2_bucket_acc.items(), key=lambda x: int(x[0])):
        per_v2_bucket[bk] = {
            'count': cnt,
            'mean_absF': s / cnt,
            'rms_absF': math.sqrt(s2 / cnt),
        }

    # --- Aggregate statistics ---
    # L2 variance: empirical variance of the hat_p values (mean-centered),
    # i.e., mean squared deviation over the *seen* residue classes.
    # By Parseval: sum_k |F[k]|^2 = q * sum_a |f[a]|^2, so
    # l2_variance_empirical = (1/n_seen) * sum_{a seen} (hat_p[a] - mean_hat_p)^2
    l2_variance_empirical = (
        sum((hat_p[a] - mean_hat_p) ** 2 for a in seen) / n_seen
        if n_seen > 0 else 0.0
    )

    # sparse_fraction_hatp: fraction of odd residue classes in [0, q) that
    # were actually sampled.  There are q/2 odd residue classes.
    n_odd_residues = q >> 1   # q / 2
    sparse_fraction_hatp = n_seen / n_odd_residues if n_odd_residues > 0 else 0.0

    # avg_rms_ratio: mean of consecutive-bucket RMS ratios rms[b+1]/rms[b]
    # across b = 0, 1, ..., M-2.  Tests the dyadic scaling of the spectrum.
    rms_by_bucket = [
        per_v2_bucket[str(b)]['rms_absF'] if str(b) in per_v2_bucket else 0.0
        for b in range(M)
    ]
    ratios = [
        rms_by_bucket[b + 1] / rms_by_bucket[b]
        for b in range(M - 1)
        if rms_by_bucket[b] > 0.0
    ]
    avg_rms_ratio = sum(ratios) / len(ratios) if ratios else float('nan')

    # --- Fourier modes rows (nonzero frequencies only) ---
    modes_rows = []
    for k in range(1, q):
        absF_k = abs(F[k])
        if absF_k > 0.0:
            modes_rows.append({
                'k': k,
                'v2k': min(v2(k), M - 1),
                'absF': absF_k,
                'ReF': F[k].real,
                'ImF': F[k].imag,
            })

    summary = {
        'observable': 'mean_log_drift',
        'M': M,
        'q': q,
        'n_residues_seen': n_seen,
        'mean_hat_p': mean_hat_p,
        'l2_variance_empirical': l2_variance_empirical,
        'sparse_fraction_hatp': sparse_fraction_hatp,
        'avg_rms_ratio': avg_rms_ratio,
        'per_v2_bucket': per_v2_bucket,
    }

    return modes_rows, summary


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def write_modes_csv(modes_rows, path):
    """Write Fourier modes to CSV."""
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, 'w', newline='') as fh:
        writer = csv.DictWriter(fh, fieldnames=['k', 'v2k', 'absF', 'ReF', 'ImF'])
        writer.writeheader()
        writer.writerows(modes_rows)


def write_json(summary, path):
    """Write summary statistics to JSON."""
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, 'w') as fh:
        json.dump(summary, fh, indent=2)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser():
    p = argparse.ArgumentParser(
        description='C9.2 Fourier analysis of per-residue mean log-drift',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument('--M', type=int, required=True,
                   help='Exponent M (must match the sampler run)')
    p.add_argument('--N', type=int, required=True,
                   help='Sample count N (used to locate input files by name)')
    p.add_argument('--input-dir', type=str, default='scripts/out',
                   help='Directory containing the sampler CSV')
    p.add_argument('--output-dir', type=str, default='scripts/out',
                   help='Directory for output files')
    p.add_argument('--csv', type=str, default=None,
                   help='Explicit path to sampler CSV (overrides --input-dir/--M/--N)')
    return p


if __name__ == '__main__':
    args = build_parser().parse_args()

    if args.csv:
        csv_path = args.csv
    else:
        csv_path = os.path.join(args.input_dir, f'c9_2_M{args.M}_N{args.N}.csv')

    json_path = os.path.join(args.output_dir, f'c9_2_M{args.M}_N{args.N}_fourier.json')
    modes_csv_path = os.path.join(
        args.output_dir, f'c9_2_M{args.M}_N{args.N}_fourier_modes.csv'
    )

    print(f"Reading sampler CSV : {csv_path}")
    hat_p = load_hat_p(csv_path)
    print(f"Residues loaded     : {len(hat_p):,}")

    modes_rows, summary = run_fourier(hat_p, M=args.M)

    write_modes_csv(modes_rows, modes_csv_path)
    write_json(summary, json_path)

    print(f"\nmean_hat_p            : {summary['mean_hat_p']:.8f}")
    print(f"(log(3/4) reference)  : {math.log(3 / 4):.8f}")
    print(f"l2_variance_empirical : {summary['l2_variance_empirical']:.8e}")
    print(f"sparse_fraction_hatp  : {summary['sparse_fraction_hatp']:.6f}")
    print(f"avg_rms_ratio         : {summary['avg_rms_ratio']:.6f}")
    print(f"\nFourier modes written : {len(modes_rows):,} nonzero frequencies")
    print(f"Output JSON  : {json_path}")
    print(f"Output CSV   : {modes_csv_path}")
