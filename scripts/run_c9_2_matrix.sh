#!/usr/bin/env bash
# run_c9_2_matrix.sh — Run C9.2 Collatz sampler + Fourier diagnostics for M=12,14,16
#
# Usage: ./scripts/run_c9_2_matrix.sh
#
# Outputs are written to scripts/out/ (not committed; attach to issues C9.2 #3 / C9.1 #10).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTPUT="${SCRIPT_DIR}/out"
mkdir -p "${OUTPUT}"

N=100000
SEED=1

for M in 12 14 16; do
    echo "=== M=${M}  N=${N} ==="

    python3 "${SCRIPT_DIR}/collatz_c9_2_sampling.py" \
        --N "${N}" \
        --M "${M}" \
        --window-type dyadic \
        --output "${OUTPUT}" \
        --seed "${SEED}"

    python3 "${SCRIPT_DIR}/collatz_c9_2_fourier.py" \
        --csv "${OUTPUT}/c9_2_M${M}_N${N}.csv" \
        --M "${M}" \
        --output "${OUTPUT}"

    echo ""
done

echo "=== All runs complete. Outputs in ${OUTPUT}/ ==="
ls -la "${OUTPUT}/"
