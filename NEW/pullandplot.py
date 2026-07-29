"""
Permian-Cushing-Gulf Coast basis: pull-and-plot sanity check
==============================================================

Step 1 of the Disaster (cusp catastrophe) test: before fitting anything,
just look at whether the price differential shows discontinuous jumps
clustered around known pipeline capacity additions, vs smooth drift.

DATA SOURCES:
- Cushing WTI spot (free): EIA Open Data API v2, series PET.RWTC.D
  -> Get a free API key at https://www.eia.gov/opendata/register.php
- Midland WTI and MEH Gulf Coast (NOT free): Argus Media proprietary
  assessments. This script expects you to supply these as a CSV with
  columns: date, midland_price, meh_price
  (source options: Bloomberg/Refinitiv terminal export, a paid Argus
  feed, or a public proxy series if you have one -- I have not verified
  any free source for these, so I'm not silently assuming one exists.)

USAGE:
    python pull_and_plot.py --eia-key YOUR_KEY --diff-csv midland_meh.csv

If you don't have the Midland/MEH CSV yet, run with just --eia-key to
confirm the Cushing pull works, and to see the pipeline milestone
annotations plotted against Cushing alone as a placeholder.
"""

import argparse
import sys
from datetime import datetime

import requests
import pandas as pd
import matplotlib.pyplot as plt

EIA_SERIES_ID = "PET.RWTC.D"  # Cushing, OK WTI Spot Price FOB, Daily

# Dated public record of major Permian takeaway pipeline in-service dates.
# Source: EIA petroleum infrastructure reports / company in-service announcements.
# Verify/update dates against current EIA reporting before relying on this list --
# I've compiled it from general knowledge of the buildout, not a single
# authoritative table, so treat these as approximate anchors to check, not fact.
PIPELINE_MILESTONES = [
    ("2019-05-01", "Gray Oak Pipeline construction start"),
    ("2019-11-01", "EPIC Crude Pipeline in service"),
    ("2020-02-01", "Gray Oak Pipeline in service"),
    ("2021-08-01", "Cactus II Pipeline in service"),
]


def fetch_cushing_wti(api_key: str, start: str = "2015-01-01") -> pd.DataFrame:
    """Pull daily Cushing WTI spot price from EIA API v2."""
    url = "https://api.eia.gov/v2/petroleum/pri/spt/data/"
    params = {
        "api_key": api_key,
        "frequency": "daily",
        "data[0]": "value",
        "facets[series][]": "RWTC",
        "start": start,
        "sort[0][column]": "period",
        "sort[0][direction]": "asc",
        "length": 5000,
    }
    resp = requests.get(url, params=params, timeout=30)
    resp.raise_for_status()
    payload = resp.json()

    if "response" not in payload or "data" not in payload["response"]:
        raise RuntimeError(f"Unexpected EIA API response shape: {payload}")

    df = pd.DataFrame(payload["response"]["data"])
    df["period"] = pd.to_datetime(df["period"])
    df = df.rename(columns={"period": "date", "value": "cushing_wti"})
    df = df[["date", "cushing_wti"]].sort_values("date").reset_index(drop=True)
    return df


def load_diff_csv(path: str) -> pd.DataFrame:
    """Load user-supplied Midland/MEH differential CSV."""
    df = pd.read_csv(path, parse_dates=["date"])
    required = {"date", "midland_price", "meh_price"}
    missing = required - set(df.columns)
    if missing:
        raise ValueError(f"CSV missing required columns: {missing}")
    return df


def plot_basis(cushing_df: pd.DataFrame, diff_df: pd.DataFrame | None, out_path: str):
    fig, ax = plt.subplots(figsize=(13, 6))

    if diff_df is not None:
        merged = pd.merge(cushing_df, diff_df, on="date", how="inner")
        merged["midland_cushing_diff"] = merged["midland_price"] - merged["cushing_wti"]
        merged["meh_cushing_diff"] = merged["meh_price"] - merged["cushing_wti"]
        ax.plot(merged["date"], merged["midland_cushing_diff"], label="Midland − Cushing", lw=1)
        ax.plot(merged["date"], merged["meh_cushing_diff"], label="MEH − Cushing", lw=1)
        ax.set_ylabel("Price differential ($/bbl)")
        ax.set_title("Permian-Cushing-Gulf Coast Basis vs Pipeline Milestones")
    else:
        ax.plot(cushing_df["date"], cushing_df["cushing_wti"], label="Cushing WTI spot", lw=1)
        ax.set_ylabel("$/bbl")
        ax.set_title("Cushing WTI (placeholder -- supply --diff-csv for actual basis)")

    for date_str, label in PIPELINE_MILESTONES:
        d = datetime.strptime(date_str, "%Y-%m-%d")
        ax.axvline(d, color="red", linestyle="--", alpha=0.5)
        ax.text(d, ax.get_ylim()[1], label, rotation=90, va="top", fontsize=7, color="red")

    ax.axhline(0, color="gray", lw=0.5)
    ax.legend()
    ax.set_xlabel("Date")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    print(f"Saved plot to {out_path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eia-key", required=True, help="Free EIA API key")
    parser.add_argument("--diff-csv", default=None,
                         help="CSV with date, midland_price, meh_price columns")
    parser.add_argument("--start", default="2015-01-01")
    parser.add_argument("--out", default="basis_plot.png")
    args = parser.parse_args()

    print("Fetching Cushing WTI from EIA...")
    cushing_df = fetch_cushing_wti(args.eia_key, start=args.start)
    print(f"Got {len(cushing_df)} rows, {cushing_df['date'].min()} to {cushing_df['date'].max()}")

    diff_df = None
    if args.diff_csv:
        print(f"Loading Midland/MEH differential from {args.diff_csv}...")
        diff_df = load_diff_csv(args.diff_csv)
    else:
        print("No --diff-csv supplied -- plotting Cushing alone as placeholder. "
              "Supply Midland/MEH data for the actual basis test.", file=sys.stderr)

    plot_basis(cushing_df, diff_df, args.out)


if __name__ == "__main__":
    main()
