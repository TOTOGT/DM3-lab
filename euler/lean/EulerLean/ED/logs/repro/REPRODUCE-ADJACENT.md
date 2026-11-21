# Reproduction record for the adjacent results (21 Nov 2026)

Scope: Theorem A (`EDbp.bp_exact`), Lemma B, the finite certificate (`EDcert`), the local-density evidence and Observation D, as stated in the paper *Adjacent results from the Euler 1747 formalization*. Nothing here proves `HPrime`; `HPrime`, `H31ndvd`, `AggTarget` stay open or conditional.

All files in this folder (`logs/repro/`) were generated on 21 Nov 2026 by re-running the commands below on the committed sources. The script hashes were checked against the repository before the runs.

## Python (run from `euler/lean/EulerLean/ED/`)

| Command | Output file | Result |
| --- | --- | --- |
| `python3 local_density_check.py` | `local_density_check.log` | 30 case lines OK, 0 MISMATCH, final line `ALL OK` |
| `python3 finite_check.py` | `finite_check.log` | `n = 2 mod 4 below 64^4: 4194304  uncovered: 0` (the script asserts 43 candidates, the last 313) |
| `python3 agg_p3_exact.py 600000` | `p3_exact_600k.log` | 200000 values, c(m) != 0 in 52930, 0 exceptions, min c/sigma = -0.5 at m = 7 |
| `python3 agg_ndvd.py A 600000` | `ndvd_A600k.log` | 14-case cross-check ALL OK, then Part A summary |
| `python3 agg_ndvd.py B` | `ndvd_B.log` | 60 (m, p) pairs, all slack >= 0 |

Script hashes (sha256, first 16 hex): `agg_ndvd.py` c3726040116fcb26, `agg_scale.py` 40c343d4a7d404d0, `agg_p3_exact.py` cd26d5619f5a57e0, `local_density_check.py` e97c9dd73524533d, `finite_check.py` a1d54d6ffdad4f46.

Environment of the re-runs: Python 3.13.18, numpy 2.5.3, sympy 1.14.0 (cloud workspace). A second environment, Python 3.10.12, numpy 2.2.6, sympy 1.14.0, is available in the desktop VM; the scripts were not re-run there. The outputs are deterministic (Part B picks its m by a fixed rule).

Comparison with the logs committed in 049ac6d: `p3_exact_600k.log` identical; `ndvd_B.log` identical in every row (only the timing lines differ); `ndvd_A600k.log` identical in the Part A summary. The committed `logs/ndvd_A600k.log` contains no cross-check block, whereas the re-run prints it first (14 pairs, ALL OK), because the committed run predates that block; the committed `logs/ndvd_A.log` (m <= 60000) contains the same 14-pair cross-check. The 14 pairs, as in the code, are (m, p) = (1,3), (5,3), (7,3), (11,3), (13,3), (17,3), (19,7), (23,7), (29,7), (35,3), (37,7), (41,3), (43,3), (47,7).

Candidate check made while preparing this record: the 43 sums x^2 + y^2 in `EDcertDefs.candCert` are exactly the 43 good numbers up to 313 (all positive integers up to 313 whose prime factors are all 1 mod 4), and each pair has gcd 1 and odd sum. The sieve in `finite_check.py` builds its candidate list independently as the good numbers a <= 313 with a = 1 mod 4 and asserts that there are 43.

## Lean 4 (environment recorded for all reports)

Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35. Mathlib revision 81a5d257c8e410db227a6665ed08f64fea08e997 (the lakefile requires tag v4.32.0).

Build order for the dependencies of the adjacent results: `StageA4o`, `Stage83` (the `ol/` folder of the audit project, `build_ol.sh`), then `Stage83cut` (imports `StageA4o`; file sha256 prefix d8a91ecfde003a12), then the modules below. Each module was compiled with

```
LEAN_PATH=$(lake env printenv LEAN_PATH):<ol folder>:<ed folder> lean -R ed -o ed/<Module>.olean ed/<Module>.lean
```

as in `build_ed.sh`; that script has the paths of the audit workspace hard-coded and has to be adapted to another machine.

| Module | Reports file | Result |
| --- | --- | --- |
| `EDbp` (Theorem A), file hash 18ca3202998f11e0 | `axioms_EDbp.txt` | `EDbp.bp_exact`: propext, Classical.choice, Quot.sound |
| `Stage83cut` lemmas used by Theorem A and Lemma B | `axioms_chain_lemmas.txt` | `Section70.hmix_of_hjac`, `Section80.hjac`, `Section81.hjac`, `FourSq.mixed_count`, `Section69.bp_card`, `Section69.bp_zero`, `Section83.bp3`, `Section83.h31ndvd_of`: each propext, Classical.choice, Quot.sound |
| `EDcert`, `EDb9k` (finite certificate) | `axioms_EDcert_EDb9k.txt` | `EDcert.good_of_sq_add_sq`, `EDcert.chunk_sound`, `EDcert.euler_finite_k`, `EDcert.euler_1747_of_H31gt3_k`, `EDb9k.euler_1747_of_hprime_k`: each propext, Classical.choice, Quot.sound. The original `EDb9.euler_1747_of_hprime` additionally lists `Euler1747.allOk_true._native.native_decide.ax_1_1` |

The `EDcert*` modules were built sequentially (see `EDCERT-REPRODUCE.md` and `logs/cert_build.log`); the reports above load those compiled modules.

## What this record still does not contain
- A run of the Python scripts on the desktop VM or any machine other than the cloud workspace.
- A build of the Lean modules outside the audit workspace; the dependency build (`StageA4o`, `Stage83`, `Stage83cut`) is described, not scripted for a fresh checkout.
- Per-theorem `#print axioms` output for the intermediate Hurwitz-quaternion lemmas behind `Section80.hjac` beyond the declaration itself.
