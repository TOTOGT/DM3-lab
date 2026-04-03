#!/usr/bin/env python3
"""
collatz_c9_2_sampling_v2.py
Stdlib-only Collatz sampling script for C9.2 empirical pipeline.
Outputs:
  - scripts/out/c9_2_M{M}_N{N}.csv
  - scripts/out/c9_2_M{M}_N{N}_summary.json
Weighted by w(n)=1/log(n). Admissible residues: odd a with v2(3a+1)=1.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import os
import random
from collections import defaultdict


def v2(n: int) -> int:
    if n == 0:
        return 0
    k = 0
    while n & 1 == 0:
        n >>= 1
        k += 1
    return k


def T_next_odd(n: int) -> int:
    m = 3 * n + 1
    return m >> v2(m)


def event_A(n: int) -> bool:
    return v2(3 * n + 1) == 1


def event_B(n: int) -> bool:
    return v2(3 * T_next_odd(n) + 1) == 1


def admissible_residues(M: int):
    mod = 1 << M
    res = []
    for a in range(1, mod, 2):
        if v2(3 * a + 1) == 1:
            res.append(a)
    return res


def ensure_out_dir(path: str):
    os.makedirs(path, exist_ok=True)


def sample_residue(a: int, M: int, N: int, window_end: int, mode: str,
                   max_samples: int, stride: int, rng: random.Random):
    mod = 1 << M
    start = N + ((a - N) % mod)
    if start < N:
        start += mod
    if mode == 'exhaustive':
        step = mod
        candidates = range(start, window_end, step)
    elif mode == 'stride':
        step = mod * stride
        candidates = range(start, window_end, step)
    elif mode == 'random':
        all_cands = list(range(start, window_end, mod))
        if len(all_cands) > max_samples:
            candidates = rng.sample(all_cands, max_samples)
        else:
            candidates = all_cands
    else:
        raise ValueError("Unknown mode")

    count_A = 0
    count_AB = 0
    weighted_A = 0.0
    weighted_AB = 0.0
    processed = 0

    for n in candidates:
        if processed >= max_samples and mode != 'random':
            break
        if n < 3:
            continue
        if not event_A(n):
            continue
        w = 1.0 / math.log(n)
        count_A += 1
        weighted_A += w
        if event_B(n):
            count_AB += 1
            weighted_AB += w
        processed += 1

    p_hat = (weighted_AB / weighted_A) if weighted_A > 0 else float('nan')
    return {
        'residue_a': a,
        'count_A': count_A,
        'count_AB': count_AB,
        'weighted_A': weighted_A,
        'weighted_AB': weighted_AB,
        'p_hat': p_hat
    }


def write_residue_csv(path: str, M: int, N: int, window_end: int, rows: list):
    with open(path, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=[
            'M', 'N', 'window_end', 'residue_a',
            'count_A', 'count_AB', 'weighted_A', 'weighted_AB', 'p_hat',
        ])
        writer.writeheader()
        for r in rows:
            writer.writerow({
                'M': M,
                'N': N,
                'window_end': window_end,
                'residue_a': r['residue_a'],
                'count_A': r['count_A'],
                'count_AB': r['count_AB'],
                'weighted_A': f"{r['weighted_A']:.12g}",
                'weighted_AB': f"{r['weighted_AB']:.12g}",
                'p_hat': f"{r['p_hat']:.12g}"
            })


def write_summary_json(path: str, summary: dict):
    with open(path, 'w') as f:
        json.dump(summary, f, indent=2)


def quantile(values: list, q: float) -> float:
    if not values:
        return float('nan')
    sv = sorted(values)
    n = len(sv)
    idx = q * (n - 1)
    lo = int(idx)
    hi = min(lo + 1, n - 1)
    frac = idx - lo
    return sv[lo] * (1 - frac) + sv[hi] * frac


def main():
    parser = argparse.ArgumentParser(description='Collatz C9.2 sampler v2')
    parser.add_argument('--M', type=int, default=4)
    parser.add_argument('--N', type=int, default=100000)
    parser.add_argument('--window-size', type=int, default=None)
    parser.add_argument('--mode', choices=['exhaustive', 'stride', 'random'], default='exhaustive')
    parser.add_argument('--stride', type=int, default=1)
    parser.add_argument('--max-samples', type=int, default=100000)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--out-dir', type=str, default='scripts/out')
    args = parser.parse_args()

    M = args.M
    N = args.N
    window_size = args.window_size if args.window_size is not None else N
    window_end = N + window_size
    mode = args.mode
    max_samples = args.max_samples
    stride = args.stride
    out_dir = args.out_dir
    rng = random.Random(args.seed)

    admissible = admissible_residues(M)
    rows = []
    total_wA = 0.0
    total_wAB = 0.0

    for a in admissible:
        stats = sample_residue(a, M, N, window_end, mode, max_samples, stride, rng)
        rows.append(stats)
        total_wA += stats['weighted_A']
        total_wAB += stats['weighted_AB']

    mean_p_overall = (total_wAB / total_wA) if total_wA > 0 else float('nan')
    valid_phats = [r['p_hat'] for r in rows if not math.isnan(r['p_hat'])]
    mean_over_residues = (sum(valid_phats) / len(valid_phats)) if valid_phats else float('nan')
    aggregate_deviation = sum(
        r['weighted_A'] / total_wA * (r['p_hat'] - 0.5)
        for r in rows
        if total_wA > 0 and not math.isnan(r['p_hat'])
    ) if total_wA > 0 else float('nan')
    max_dev = max(abs(p - 0.5) for p in valid_phats) if valid_phats else float('nan')
    qs = {
        '25': quantile(valid_phats, 0.25),
        '50': quantile(valid_phats, 0.50),
        '75': quantile(valid_phats, 0.75),
        '90': quantile(valid_phats, 0.90),
        '95': quantile(valid_phats, 0.95),
    }

    summary = {
        'M': M,
        'N': N,
        'window_end': window_end,
        'mean_p_overall': mean_p_overall,
        'mean_p_over_residues': mean_over_residues,
        'max_deviation_per_residue': max_dev,
        'aggregate_signed_deviation_D_N': aggregate_deviation,
        'p_hat_quantiles': qs,
        'n_admissible': len(admissible),
        'mode': mode,
        'max_samples_per_residue': max_samples,
        'seed': args.seed
    }

    ensure_out_dir(out_dir)
    residue_path = os.path.join(out_dir, f'c9_2_M{M}_N{N}.csv')
    summary_path = os.path.join(out_dir, f'c9_2_M{M}_N{N}_summary.json')

    write_residue_csv(residue_path, M, N, window_end, rows)
    write_summary_json(summary_path, summary)

    print("Wrote:", residue_path)
    print("Wrote:", summary_path)


if __name__ == '__main__':
    main()
