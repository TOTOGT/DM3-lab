#!/usr/bin/env python3
"""
C9.2 Fourier Diagnostics — Spectral analysis of hat_p over dyadic residue classes.

Reads the CSV produced by collatz_c9_2_sampling.py, computes the real DFT of
hat_p ordered by residue, identifies dominant modes, measures spectral entropy,
and produces diagnostic plots.

Outputs
-------
  <out>/c9_2_M{M}_N{N}_fourier.json           full spectral metrics
  <out>/c9_2_M{M}_N{N}_fourier_modes.csv      top-K mode table
  <out>/c9_2_M{M}_N{N}_fourier_spectrum.png   log power spectrum
  <out>/c9_2_M{M}_N{N}_fourier_reconstr.png   top-mode reconstruction

G6 LLC · Pablo Nogueira Grossi · Newark NJ · 2026
MIT License
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


# ── I/O ──────────────────────────────────────────────────────────────────────

def read_csv(csv_path: Path) -> list[dict]:
    rows: list[dict] = []
    with open(csv_path, newline="") as fh:
        for row in csv.DictReader(fh):
            rows.append({
                "residue":   int(row["residue"]),
                "hat_p":     float(row["hat_p"]),
                "residual":  float(row["residual"]),
                "v2":        int(row["v2"]),
                "n_samples": int(row["n_samples"]),
            })
    return rows


def infer_M_N(stem: str) -> tuple[int, int]:
    m = re.search(r"M(\d+)", stem)
    n = re.search(r"N(\d+)", stem)
    return (int(m.group(1)) if m else 0), (int(n.group(1)) if n else 0)


# ── main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="C9.2 Fourier diagnostics")
    parser.add_argument("--csv",       required=True, help="Input CSV from sampling script")
    parser.add_argument("--output",    default="scripts/out")
    parser.add_argument("--top-modes", type=int, default=10,
                        help="Number of dominant modes to report")
    args = parser.parse_args()

    csv_path = Path(args.csv)
    out_dir  = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)

    M, N = infer_M_N(csv_path.stem)
    print(f"[Fourier] M={M}  N={N:,}  csv={csv_path.name}")

    rows = read_csv(csv_path)
    if not rows:
        raise RuntimeError("Empty CSV — nothing to analyse.")

    rows.sort(key=lambda r: r["residue"])

    residues  = np.array([r["residue"]  for r in rows], dtype=np.float64)
    hat_p     = np.array([r["hat_p"]    for r in rows], dtype=np.float64)
    n_samples = np.array([r["n_samples"] for r in rows], dtype=np.int64)

    n_classes  = len(rows)
    mean_hat_p = float(np.mean(hat_p))

    # DFT of mean-centred hat_p
    signal     = hat_p - mean_hat_p
    fft_coeffs = np.fft.rfft(signal)                   # complex, len = n//2+1
    freqs      = np.fft.rfftfreq(n_classes)            # cycles per class
    power      = np.abs(fft_coeffs) ** 2

    total_power = float(np.sum(power[1:]))             # skip DC (index 0)

    # Top-K modes (exclude DC at index 0)
    k         = min(args.top_modes, len(power) - 1)
    top_idx   = np.argsort(power[1:])[::-1][:k] + 1   # +1 to restore original index
    top_power = float(np.sum(power[top_idx]))

    modes: list[dict] = []
    for idx in top_idx:
        f = float(freqs[idx])
        modes.append({
            "mode_index":     int(idx),
            "frequency":      round(f, 8),
            "period_classes": round(1.0 / f, 3) if f > 0 else None,
            "power":          round(float(power[idx]), 8),
            "power_fraction": round(float(power[idx] / total_power), 8)
                              if total_power > 0 else 0.0,
            "amplitude":      round(float(np.abs(fft_coeffs[idx])), 8),
            "phase_rad":      round(float(np.angle(fft_coeffs[idx])), 8),
        })

    # Spectral entropy (normalised; excludes DC)
    p_norm          = power[1:] / total_power if total_power > 0 else power[1:]
    p_pos           = p_norm[p_norm > 0]
    spectral_ent    = float(-np.sum(p_pos * np.log(p_pos))) if len(p_pos) > 0 else 0.0
    max_ent         = float(np.log(len(power) - 1)) if len(power) > 1 else 1.0
    normalised_ent  = spectral_ent / max_ent if max_ent > 0 else 0.0

    result = {
        "M":                  M,
        "N":                  N,
        "n_classes":          n_classes,
        "mean_hat_p":         round(mean_hat_p, 8),
        "total_power":        round(total_power, 8),
        "spectral_entropy":   round(spectral_ent, 8),
        "normalised_entropy": round(normalised_ent, 8),
        "top_power_fraction": round(top_power / total_power, 8)
                              if total_power > 0 else 0.0,
        "top_modes":          modes,
    }

    # ── Fourier JSON ─────────────────────────────────────────────────────────
    json_path = out_dir / f"c9_2_M{M}_N{N}_fourier.json"
    with open(json_path, "w") as fh:
        json.dump(result, fh, indent=2)
    print(f"  JSON: {json_path}")

    # ── Modes CSV ────────────────────────────────────────────────────────────
    modes_csv = out_dir / f"c9_2_M{M}_N{N}_fourier_modes.csv"
    with open(modes_csv, "w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=[
            "mode_index","frequency","period_classes",
            "power","power_fraction","amplitude","phase_rad",
        ])
        writer.writeheader()
        writer.writerows(modes)
    print(f"  Modes CSV: {modes_csv}")

    # ── Plot 1: log power spectrum ────────────────────────────────────────────
    fig, ax = plt.subplots(figsize=(10, 4))
    ax.semilogy(freqs[1:], power[1:], lw=0.7, color="steelblue", label="power")
    for mode in modes[:5]:
        idx = mode["mode_index"]
        ax.axvline(freqs[idx], color="red", alpha=0.5, lw=1, ls="--")
    ax.set_xlabel("Frequency (cycles per residue class)")
    ax.set_ylabel("Power  (log scale)")
    ax.set_title(f"C9.2 Fourier power spectrum  |  M={M}  N={N:,}")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(fontsize=8)
    png1 = out_dir / f"c9_2_M{M}_N{N}_fourier_spectrum.png"
    fig.tight_layout()
    fig.savefig(png1, dpi=120)
    plt.close(fig)
    print(f"  Plot: {png1}")

    # ── Plot 2: top-mode reconstruction ──────────────────────────────────────
    top_k      = min(5, len(modes))
    fft_masked = np.zeros_like(fft_coeffs)
    for mode in modes[:top_k]:
        fft_masked[mode["mode_index"]] = fft_coeffs[mode["mode_index"]]
    reconstr   = np.fft.irfft(fft_masked, n=n_classes) + mean_hat_p

    fig, ax = plt.subplots(figsize=(10, 4))
    ax.scatter(residues, hat_p, s=1, alpha=0.35, color="gray", label="data")
    ax.plot(residues, reconstr, lw=1.4, color="red",
            label=f"top-{top_k} reconstruction")
    ax.axhline(mean_hat_p, color="black", lw=1, ls="--",
               label=f"mean = {mean_hat_p:.4f}")
    ax.set_xlabel("Residue r = n mod 2^M")
    ax.set_ylabel("hat_p(r)")
    ax.set_title(f"C9.2 Fourier reconstruction  |  M={M}  N={N:,}")
    ax.legend(fontsize=8)
    png2 = out_dir / f"c9_2_M{M}_N{N}_fourier_reconstr.png"
    fig.tight_layout()
    fig.savefig(png2, dpi=120)
    plt.close(fig)
    print(f"  Plot: {png2}")

    # ── console ───────────────────────────────────────────────────────────────
    print(f"  spectral_entropy (norm) = {normalised_ent:.4f}")
    print(f"  top-{k} power fraction  = {result['top_power_fraction']:.4f}")
    print(f"  dominant mode: index={modes[0]['mode_index']}  "
          f"period={modes[0]['period_classes']}  "
          f"frac={modes[0]['power_fraction']:.4f}")


if __name__ == "__main__":
    main()
