#!/usr/bin/env python3
"""
scripts/collatz_c9_2_sampling_option1.py

C9.2 Option 1 sampler: estimates hat_p(a) for residue classes a mod 2^M.

Observable:
  Event A: n is odd.
  Event B: T(n) < n, where T(n) = (3n+1) / 2^{v2(3n+1)} for odd n.
  hat_p(a) = P(B | A, n ≡ a mod 2^M)
           = (# odd n ≡ a with T(n)<n) / (# odd n ≡ a sampled)

Modes:
  exhaustive: iterate odd integers 1,3,5,... up to window-size,
              stopping early at max-samples total odd integers processed.
  random:     draw random odd integers from [1, window-size],
              stopping at max-samples total draws.

Output:
  CSV: scripts/out/c9_2_M{M}_N{N}.csv
  Columns: residue_a, count_A, count_B, hat_p
  (Residues with no observations are omitted → hat_p undefined.)

CLI:
  python3 scripts/collatz_c9_2_sampling_option1.py \
    --M 8 --N 10000 --window-size 10000 --mode exhaustive \
    --max-samples 5000 --seed 1 --out-dir scripts/out
"""

from __future__ import annotations

import argparse
import csv
import os
import random


def v2_int(x: int) -> int:
    """2-adic valuation of x (x > 0)."""
    if x == 0:
        return 10 ** 9
    v = 0
    while (x & 1) == 0:
        x >>= 1
        v += 1
    return v


def event_B(n: int) -> bool:
    """True iff T(n) < n for odd n, where T(n) = (3n+1) / 2^{v2(3n+1)}."""
    k = v2_int(3 * n + 1)
    t = (3 * n + 1) >> k
    return t < n


def main() -> int:
    ap = argparse.ArgumentParser(description="C9.2 Option 1 sampler")
    ap.add_argument("--M", type=int, required=True, help="Exponent: q = 2^M")
    ap.add_argument("--N", type=int, required=True, help="Sample count label (used in filename)")
    ap.add_argument("--window-size", type=int, default=None,
                    help="Upper bound on odd integers sampled (defaults to N)")
    ap.add_argument("--mode", choices=["exhaustive", "random"], default="exhaustive")
    ap.add_argument("--max-samples", type=int, default=None,
                    help="Hard limit on number of odd integers processed")
    ap.add_argument("--seed", type=int, default=None, help="Random seed (for random mode)")
    ap.add_argument("--out-dir", default="scripts/out", help="Output directory")
    args = ap.parse_args()

    if args.seed is not None:
        random.seed(args.seed)

    q = 1 << args.M
    window = args.window_size if args.window_size is not None else args.N
    max_s = args.max_samples if args.max_samples is not None else (window + 1) // 2

    count_A = [0] * q
    count_B = [0] * q

    os.makedirs(args.out_dir, exist_ok=True)

    if args.mode == "exhaustive":
        processed = 0
        n = 1
        while n <= window and processed < max_s:
            a = n % q
            count_A[a] += 1
            if event_B(n):
                count_B[a] += 1
            processed += 1
            n += 2
    else:
        # random: draw odd integers uniformly from [1, window]
        max_odd = (window - 1) | 1  # largest odd <= window
        processed = 0
        while processed < max_s:
            n = random.randrange(1, max_odd + 1, 2)
            a = n % q
            count_A[a] += 1
            if event_B(n):
                count_B[a] += 1
            processed += 1

    out_csv = os.path.join(args.out_dir, f"c9_2_M{args.M}_N{args.N}.csv")
    with open(out_csv, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["residue_a", "count_A", "count_B", "hat_p"])
        for a in range(q):
            if count_A[a] > 0:
                hat_p = count_B[a] / count_A[a]
                w.writerow([a, count_A[a], count_B[a], hat_p])

    print(f"Wrote: {out_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
