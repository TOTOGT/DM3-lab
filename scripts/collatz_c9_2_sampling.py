"""
C9.2 Monte-Carlo sampling for consecutive (1,1) Collatz parity probabilities
weighted by the contact-form weight w(n) = 1/log(n).

Background
----------
For odd n we define the half-step map  T(n) = (3n+1)//2.
The "11 event" is: n is odd AND T(n) is odd.
T(n) is odd iff n ≡ 3 (mod 4), so under the uniform measure on odd integers
the unconditional probability is exactly 1/2.

Under the contact-form weight w(n) ≈ 1/log(n) the weighted p11 may differ
from 1/2 for finite windows, and the rate of convergence is the observable of
interest (decorrelation hypothesis).

For the finite-range checks we additionally run the *full* standard Collatz
map T_full(n) = n//2 (even) or 3n+1 (odd) for `depth` steps and record the
complete parity orbit b_0, b_1, ..., b_{depth-1}.  Because consecutive
odd→even is deterministic (odd n always yields even 3n+1), genuine "11"
patterns in the parity orbit only appear at positions k where b_{k-1}=0,
so we report the auto-correlation function C(lag) = Cov(b_k, b_{k+lag}).

Usage
-----
    python scripts/collatz_c9_2_sampling.py \\
        --start 33 --end 100000 --M 100000 \\
        --depth 20 --seed 42 --output scripts/out
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

def weight(n):
    """Contact-form weight w(n) = 1 / log(n).  Defined for n >= 3."""
    return 1.0 / math.log(n)


def half_step(n):
    """Half-step accelerated map for odd n:  T(n) = (3n+1) // 2.
    Result is odd iff n ≡ 3 (mod 4)."""
    return (3 * n + 1) // 2


def v2(n):
    """2-adic valuation of n (number of trailing zero bits)."""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        n //= 2
        count += 1
    return count


def full_step(n):
    """Standard single-step Collatz map."""
    if n % 2 == 1:
        return 3 * n + 1
    return n // 2


def parity_orbit(n, depth):
    """Return list of parity bits [b_0, ..., b_{depth-1}] along the full
    Collatz orbit starting from n.  Once the orbit reaches 1 it continues
    cycling 1 → 4 → 2 → 1 with parity pattern [1, 0, 0, 1, 0, 0, ...]."""
    bits = []
    cur = n
    for _ in range(depth):
        bits.append(cur % 2)
        if cur == 1:
            # Fill remaining positions with the repeating 1-cycle parity: 1,0,0
            cycle = [1, 0, 0]
            remaining = depth - len(bits)
            for j in range(remaining):
                bits.append(cycle[j % 3])
            break
        cur = full_step(cur)
    return bits


# ---------------------------------------------------------------------------
# Sampling
# ---------------------------------------------------------------------------

def run_sampling(start, end, M, depth, seed=None):
    """Sample M odd integers uniformly from [start, end] and compute
    weighted statistics for the decorrelation hypothesis.

    Parameters
    ----------
    start, end : int
        Window bounds (start is rounded up to the nearest odd >= 33).
    M : int
        Number of Monte-Carlo draws.
    depth : int
        Length of the full-Collatz parity orbit recorded per sample.
    seed : int or None
        RNG seed for reproducibility.

    Returns
    -------
    samples : list[dict]
        One dict per draw; keys: n, w, b1_half, parities.
    summary : dict
        Aggregate statistics including p11, p_k, convergence checkpoints,
        and the auto-correlation function.
    """
    if seed is not None:
        random.seed(seed)

    # Enforce odd bounds >= 33
    start = max(start, 33)
    if start % 2 == 0:
        start += 1
    if end % 2 == 0:
        end -= 1

    n_odd = (end - start) // 2 + 1  # count of odd integers in [start, end]
    if n_odd <= 0:
        raise ValueError(f"Empty window after adjustments: start={start}, end={end}")

    samples = []

    # Accumulators (all weighted)
    total_w = 0.0
    w_b1_half = 0.0                       # weight * b1_half  (the "11" indicator)
    w_bk = [0.0] * depth                  # weight * b_k  for each orbit position
    w_bk_bj = [[0.0] * depth for _ in range(depth)]  # weight * b_k * b_j

    # Convergence checkpoints at ~100 intervals
    checkpoint_interval = max(1, M // 100)
    convergence = []
    running_w = 0.0
    running_w_b1 = 0.0

    for i in range(M):
        # Uniform random odd integer in [start, end]
        idx = random.randint(0, n_odd - 1)
        n = start + 2 * idx

        w_n = weight(n)
        hs = half_step(n)
        b1_half = hs % 2   # 1 iff n ≡ 3 (mod 4)  →  the "11" indicator

        orbit = parity_orbit(n, depth)

        # Accumulate
        total_w += w_n
        w_b1_half += w_n * b1_half
        running_w += w_n
        running_w_b1 += w_n * b1_half

        for k, bk in enumerate(orbit):
            w_bk[k] += w_n * bk
            for j, bj in enumerate(orbit):
                w_bk_bj[k][j] += w_n * bk * bj

        samples.append({
            'n': n,
            'w': w_n,
            'b1_half': b1_half,
            'parities': orbit,
        })

        # Convergence checkpoint
        if (i + 1) % checkpoint_interval == 0:
            p11_now = running_w_b1 / running_w if running_w > 0 else 0.0
            convergence.append({'sample_count': i + 1, 'p11': p11_now})

    # --- Summary statistics ---
    p11 = w_b1_half / total_w if total_w > 0 else 0.0

    # Marginal p_k = weighted P(b_k = 1)
    p_k = [w_bk[k] / total_w for k in range(depth)]

    # Auto-correlation function anchored at position 2, the first non-degenerate
    # orbit position (b_0 = 1 always; b_1 = 0 always for odd starting n under
    # the full Collatz map, so both have zero variance).
    # C(lag) = Cor(b_2, b_{2+lag})  for lag = 0, 1, ..., depth-3.
    ref = 2  # anchor position
    acf = []
    for lag in range(depth - ref):
        j = ref + lag
        p_ref = p_k[ref]
        p_j   = p_k[j]
        e_ref_j = w_bk_bj[ref][j] / total_w if total_w > 0 else 0.0
        cov = e_ref_j - p_ref * p_j
        var_ref = p_ref * (1.0 - p_ref)
        var_j   = p_j   * (1.0 - p_j)
        denom = math.sqrt(var_ref * var_j) if var_ref > 0 and var_j > 0 else 0.0
        acf.append(cov / denom if denom > 0 else 0.0)

    summary = {
        'start': start,
        'end': end,
        'M': M,
        'depth': depth,
        'seed': seed,
        'total_weight': total_w,
        'p11': p11,
        'p11_expected_uniform': 0.5,
        'deviation_from_uniform': p11 - 0.5,
        'p_k': p_k,
        'acf': acf,
        'convergence': convergence,
    }

    return samples, summary


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def write_csv(samples, path, depth):
    """Write raw sample data to a CSV file."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    fieldnames = ['n', 'w', 'b1_half'] + [f'b{k}' for k in range(depth)]
    with open(path, 'w', newline='') as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        for s in samples:
            row = {'n': s['n'], 'w': f"{s['w']:.8e}", 'b1_half': s['b1_half']}
            for k, bk in enumerate(s['parities']):
                row[f'b{k}'] = bk
            writer.writerow(row)


def write_json(summary, path):
    """Write summary statistics to a JSON file."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as fh:
        json.dump(summary, fh, indent=2)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def build_parser():
    p = argparse.ArgumentParser(
        description='C9.2 weighted Monte-Carlo sampling for Collatz (1,1) probabilities',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument('--start', type=int, default=33,
                   help='Lower bound of sampling window (rounded to odd >= 33)')
    p.add_argument('--end', type=int, default=100_000,
                   help='Upper bound of sampling window (rounded to odd)')
    p.add_argument('--M', type=int, default=100_000,
                   help='Number of Monte-Carlo draws')
    p.add_argument('--depth', type=int, default=20,
                   help='Length of full-Collatz parity orbit per sample')
    p.add_argument('--seed', type=int, default=None,
                   help='RNG seed for reproducibility')
    p.add_argument('--output', type=str, default='scripts/out',
                   help='Directory for output files')
    return p


if __name__ == '__main__':
    args = build_parser().parse_args()

    tag = f'start{args.start}_end{args.end}_M{args.M}'
    csv_path = os.path.join(args.output, f'c9_2_{tag}.csv')
    json_path = os.path.join(args.output, f'c9_2_{tag}_summary.json')

    print(f"Sampling window  : [{args.start}, {args.end}]  odd integers")
    print(f"Draws M          : {args.M:,}")
    print(f"Orbit depth      : {args.depth}")
    print(f"Seed             : {args.seed}")

    samples, summary = run_sampling(
        start=args.start,
        end=args.end,
        M=args.M,
        depth=args.depth,
        seed=args.seed,
    )

    write_csv(samples, csv_path, args.depth)
    write_json(summary, json_path)

    print(f"\nResults")
    print(f"  p11  (weighted) = {summary['p11']:.6f}")
    print(f"  p11  (expected) = {summary['p11_expected_uniform']:.6f}")
    print(f"  deviation       = {summary['deviation_from_uniform']:+.6f}")
    print(f"\nOutput CSV  : {csv_path}")
    print(f"Output JSON : {json_path}")
