"""
C9.2 graded-drift sampler — dyadic window, per-residue mean log-drift.

For each of N random draws from odd n in the dyadic window [2^(M-1), 2^M):
  - Computes v2x = v2(3n+1)
  - Computes T(n) = (3n+1) // 2^v2x  (odd-to-odd Syracuse step)
  - Computes log_drift(n) = log(T(n)/n)
  - Records residue a = n mod 2^M  (= n for n in the dyadic window)
  - Buckets by v2x

Aggregates per-residue statistics and writes:
  - CSV: a, mean_log_drift, count
  - JSON summary: global_mean_log_drift, residue_mean_of_means, per_v2_bucket, ...

Usage
-----
    python scripts/collatz_c9_2_sampling.py --M 12 --N 100000 --seed 42 \\
        --output-dir scripts/out
"""

import argparse
import csv
import json
import math
import os
import random


# ---------------------------------------------------------------------------
# Core Collatz helpers
# ---------------------------------------------------------------------------

def v2(n: int) -> int:
    """2-adic valuation: largest k such that 2^k divides n."""
    if n == 0:
        return 0
    count = 0
    while n % 2 == 0:
        n >>= 1
        count += 1
    return count


def T_odd(n: int) -> tuple:
    """
    Odd-to-odd Syracuse step.

    Returns (T(n), v2x) where T(n) = (3n+1) // 2^v2x and v2x = v2(3n+1).
    For odd n, 3n+1 is always even, so v2x >= 1.
    """
    m = 3 * n + 1
    v2x = v2(m)
    return m >> v2x, v2x


# ---------------------------------------------------------------------------
# Sampler
# ---------------------------------------------------------------------------

def run_sampler(M: int, N: int, seed=None):
    """
    Sample N odd integers uniformly from the dyadic window [2^(M-1), 2^M) and
    compute per-residue mean log-drift statistics.

    Parameters
    ----------
    M : int
        Exponent; dyadic window is [2^(M-1), 2^M).  Requires M >= 2.
    N : int
        Number of random draws (with replacement).
    seed : int or None
        RNG seed for reproducibility.

    Returns
    -------
    rows : list[dict]
        One dict per seen residue class: {a, mean_log_drift, count}.
    summary : dict
        Aggregate statistics.
    """
    if M < 2:
        raise ValueError("M must be >= 2")
    if seed is not None:
        random.seed(seed)

    lo = 1 << (M - 1)   # 2^(M-1); always even (M >= 2 is enforced above)
    hi = 1 << M          # 2^M

    # Odd integers in [lo, hi): lo is even, so first odd is lo+1 = 2^(M-1)+1.
    # They are:  lo+1, lo+3, ..., hi-1.
    # Count = (hi-1 - (lo+1)) // 2 + 1 = (2^M - 2 - 2^(M-1)) // 2 + 1 = 2^(M-2).
    first_odd = lo + 1
    n_odd_in_window = (hi - first_odd) // 2 + 1  # = 2^(M-2)

    # Per-residue accumulators  {a: [sum_log_drift, count]}
    residue_acc = {}

    # Per-v2-bucket accumulators  {v2x: [sum, sum_sq, count]}
    v2_bucket_acc = {}

    total_log = 0.0

    for _ in range(N):
        idx = random.randrange(n_odd_in_window)
        n = first_odd + 2 * idx

        Tn, v2x = T_odd(n)
        log_drift = math.log(Tn / n)

        # Residue: a = n mod 2^M.  Since n in [lo, hi) ⊂ [0, 2^M), a = n.
        a = n

        if a in residue_acc:
            residue_acc[a][0] += log_drift
            residue_acc[a][1] += 1
        else:
            residue_acc[a] = [log_drift, 1]

        if v2x in v2_bucket_acc:
            v2_bucket_acc[v2x][0] += log_drift
            v2_bucket_acc[v2x][1] += log_drift * log_drift
            v2_bucket_acc[v2x][2] += 1
        else:
            v2_bucket_acc[v2x] = [log_drift, log_drift * log_drift, 1]

        total_log += log_drift

    # Finalize per-residue means
    rows = []
    for a in sorted(residue_acc):
        s, c = residue_acc[a]
        mean_ld = s / c
        residue_acc[a] = mean_ld   # store final mean for summary computation
        rows.append({'a': a, 'mean_log_drift': mean_ld, 'count': c})

    # global_mean_log_drift: integer-weighted mean over all N draws
    global_mean_log_drift = total_log / N if N > 0 else float('nan')

    # residue_mean_of_means: mean over seen residue classes (residue-weighted)
    n_seen = len(rows)
    residue_mean_of_means = (
        sum(r['mean_log_drift'] for r in rows) / n_seen
        if n_seen > 0 else float('nan')
    )

    # Per-v2-bucket summary
    per_v2_bucket = {}
    for v2x in sorted(v2_bucket_acc):
        s, s2, cnt = v2_bucket_acc[v2x]
        mean_val = s / cnt
        rms_val = math.sqrt(s2 / cnt)
        per_v2_bucket[str(v2x)] = {
            'count': cnt,
            'mean_log_drift': mean_val,
            'rms_log_drift': rms_val,
            'fraction': cnt / N,
        }

    summary = {
        'observable': 'mean_log_drift',
        'M': M,
        'N': N,
        'seed': seed,
        'dyadic_window': [lo, hi - 1],
        'n_odd_in_window': n_odd_in_window,
        'n_residues_seen': n_seen,
        'global_mean_log_drift': global_mean_log_drift,
        'residue_mean_of_means': residue_mean_of_means,
        'per_v2_bucket': per_v2_bucket,
    }

    return rows, summary


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def write_csv(rows, path):
    """Write per-residue data to CSV."""
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, 'w', newline='') as fh:
        writer = csv.DictWriter(fh, fieldnames=['a', 'mean_log_drift', 'count'])
        writer.writeheader()
        writer.writerows(rows)


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
        description='C9.2 graded-drift sampler: per-residue mean log-drift on a dyadic window',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument('--M', type=int, required=True,
                   help='Exponent: dyadic window is [2^(M-1), 2^M)')
    p.add_argument('--N', type=int, required=True,
                   help='Number of random draws (with replacement)')
    p.add_argument('--seed', type=int, default=None,
                   help='RNG seed for reproducibility')
    p.add_argument('--output-dir', type=str, default='scripts/out',
                   help='Directory for output files')
    return p


if __name__ == '__main__':
    args = build_parser().parse_args()

    out_dir = args.output_dir
    csv_path = os.path.join(out_dir, f'c9_2_M{args.M}_N{args.N}.csv')
    json_path = os.path.join(out_dir, f'c9_2_M{args.M}_N{args.N}_summary.json')

    print(f"Dyadic window : [2^{args.M - 1}, 2^{args.M}) = [{1 << (args.M - 1)}, {(1 << args.M) - 1}]")
    print(f"Draws N       : {args.N:,}")
    print(f"Seed          : {args.seed}")

    rows, summary = run_sampler(M=args.M, N=args.N, seed=args.seed)

    write_csv(rows, csv_path)
    write_json(summary, json_path)

    print(f"\nResidues seen         : {summary['n_residues_seen']:,} / {summary['n_odd_in_window']:,}")
    print(f"global_mean_log_drift : {summary['global_mean_log_drift']:.8f}")
    print(f"residue_mean_of_means : {summary['residue_mean_of_means']:.8f}")
    print(f"(log(3/4) reference)  : {math.log(3 / 4):.8f}")
    print(f"\nOutput CSV  : {csv_path}")
    print(f"Output JSON : {json_path}")
