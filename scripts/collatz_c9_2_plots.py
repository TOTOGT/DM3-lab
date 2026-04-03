"""
C9.2 Plot generation for Monte-Carlo results.

Reads a JSON summary produced by collatz_c9_2_sampling.py and saves:

  convergence_<tag>.png  — p11 vs. sample count (convergence plot)
  acf_<tag>.png          — auto-correlation C(lag) of the parity orbit
  marginals_<tag>.png    — marginal P(b_k = 1) for each orbit position k

Usage
-----
    # Run sampling first (produces the JSON summary):
    python scripts/collatz_c9_2_sampling.py --start 33 --end 1000000 \\
        --M 1000000 --depth 20 --seed 0 --output scripts/out

    # Then generate plots:
    python scripts/collatz_c9_2_plots.py \\
        --summary scripts/out/c9_2_start33_end1000000_M1000000_summary.json \\
        --output  scripts/out
"""

import argparse
import json
import os

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


# ---------------------------------------------------------------------------
# Individual plot functions
# ---------------------------------------------------------------------------

def plot_convergence(summary, outdir, tag):
    """p11 vs. sample count with a horizontal reference line at 0.5."""
    conv = summary.get('convergence', [])
    if not conv:
        print("  [convergence] no data — skipping")
        return

    counts = [c['sample_count'] for c in conv]
    p11s   = [c['p11'] for c in conv]

    fig, ax = plt.subplots(figsize=(8, 4))
    ax.plot(counts, p11s, lw=1.2, color='steelblue', label='p₁₁ (weighted)')
    ax.axhline(0.5, color='crimson', lw=1, ls='--', label='Expected 0.5 (uniform)')

    ax.set_xlabel('Sample count')
    ax.set_ylabel('p₁₁')
    ax.set_title(
        f'Convergence of p₁₁  |  window [{summary["start"]}, {summary["end"]}]  '
        f'M = {summary["M"]:,}'
    )
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.tight_layout()

    path = os.path.join(outdir, f'convergence_{tag}.png')
    fig.savefig(path, dpi=120)
    plt.close(fig)
    print(f"  saved {path}")


def plot_acf(summary, outdir, tag):
    """Auto-correlation function C(lag) = Cor(b_2, b_{2+lag}) of the parity orbit."""
    acf = summary.get('acf', [])
    if not acf:
        print("  [acf] no data — skipping")
        return

    lags = list(range(len(acf)))

    fig, ax = plt.subplots(figsize=(8, 4))
    ax.bar(lags, acf, color='steelblue', alpha=0.7, label='ACF C(lag)')
    ax.axhline(0.0, color='black', lw=0.8)

    # 95 % confidence band under H0 (iid)
    n_samples = summary['M']
    ci = 1.96 / n_samples ** 0.5
    ax.axhline( ci, color='crimson', lw=1, ls='--', label='±1.96/√M (95 % CI)')
    ax.axhline(-ci, color='crimson', lw=1, ls='--')

    ax.set_xlabel('Lag  (C(lag) = Cor(b₂, b_{2+lag}))')
    ax.set_ylabel('Correlation')
    ax.set_title(
        f'Parity-orbit auto-correlation  |  window [{summary["start"]}, {summary["end"]}]  '
        f'M = {summary["M"]:,}'
    )
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.tight_layout()

    path = os.path.join(outdir, f'acf_{tag}.png')
    fig.savefig(path, dpi=120)
    plt.close(fig)
    print(f"  saved {path}")


def plot_marginals(summary, outdir, tag):
    """Marginal P(b_k = 1) for each orbit position k."""
    p_k = summary.get('p_k', [])
    if not p_k:
        print("  [marginals] no data — skipping")
        return

    positions = list(range(len(p_k)))

    fig, ax = plt.subplots(figsize=(8, 4))
    ax.bar(positions, p_k, color='steelblue', alpha=0.7)
    ax.axhline(0.5, color='crimson', lw=1, ls='--', label='0.5 reference')

    ax.set_xlabel('Orbit position k')
    ax.set_ylabel('P(b_k = 1) weighted')
    ax.set_title(
        f'Marginal parity probabilities  |  window [{summary["start"]}, {summary["end"]}]  '
        f'M = {summary["M"]:,}'
    )
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')
    fig.tight_layout()

    path = os.path.join(outdir, f'marginals_{tag}.png')
    fig.savefig(path, dpi=120)
    plt.close(fig)
    print(f"  saved {path}")


def plot_multi_window_comparison(summaries, labels, outdir):
    """Overlay convergence curves from multiple window/M experiments."""
    fig, ax = plt.subplots(figsize=(9, 5))

    colors = plt.cm.tab10(np.linspace(0, 0.9, len(summaries)))

    for summary, label, color in zip(summaries, labels, colors):
        conv = summary.get('convergence', [])
        if not conv:
            continue
        counts = [c['sample_count'] for c in conv]
        p11s   = [c['p11'] for c in conv]
        ax.plot(counts, p11s, lw=1.2, color=color, label=label)

    ax.axhline(0.5, color='black', lw=1.2, ls='--', label='Expected 0.5')
    ax.set_xlabel('Sample count')
    ax.set_ylabel('p₁₁')
    ax.set_title('Multi-window convergence comparison')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()

    path = os.path.join(outdir, 'multi_window_convergence.png')
    fig.savefig(path, dpi=120)
    plt.close(fig)
    print(f"  saved {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser():
    p = argparse.ArgumentParser(
        description='Generate plots from C9.2 sampling JSON summaries',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    p.add_argument('--summary', nargs='+', required=True,
                   help='Path(s) to JSON summary file(s) from collatz_c9_2_sampling.py')
    p.add_argument('--output', type=str, default='scripts/out',
                   help='Directory for output PNG files')
    return p


if __name__ == '__main__':
    args = build_parser().parse_args()
    os.makedirs(args.output, exist_ok=True)

    summaries = []
    labels = []

    for json_path in args.summary:
        with open(json_path) as fh:
            s = json.load(fh)
        summaries.append(s)

        tag = (
            f"start{s['start']}_end{s['end']}_M{s['M']}"
        )
        labels.append(f"[{s['start']},{s['end']}] M={s['M']:,}")

        print(f"\nProcessing {json_path}  (tag={tag})")
        plot_convergence(s, args.output, tag)
        plot_acf(s, args.output, tag)
        plot_marginals(s, args.output, tag)

    if len(summaries) > 1:
        print("\nGenerating multi-window comparison plot …")
        plot_multi_window_comparison(summaries, labels, args.output)

    print("\nDone.")
