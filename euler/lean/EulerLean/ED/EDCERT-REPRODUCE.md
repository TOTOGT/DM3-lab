# EDcert reproducibility record

Status: kernel-checked finite range (EDcert) plus conditional theorem `EDb9k.euler_1747_of_hprime_k`.
`HPrime`, `H31ndvd`, `AggTarget` are unchanged and remain open/conditional. The original
`EDb9.euler_1747_of_hprime` is untouched (it still carries the native_decide axiom).

## Toolchain (as built)
- Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35
- Mathlib rev 81a5d257c8e410db227a6665ed08f64fea08e997 (lakefile requires tag "v4.32.0")
- Peak memory about 5 GB; the environment limit was 8 GB. Total build about 45 minutes.

## Build (strictly sequential; parallel or 32-chunk builds were OOM-killed, RC 137)
Script: `build_cert_seq.sh` (runs `lean -R ed -o ed/<M>.olean ed/<M>.lean` per module,
logging `<M> RC <code> SECS <n>` to `ed/cert.log`). Order:

    EDcertDefs EDcertC1 EDcertD0 EDcertD1 ... EDcertD13 EDcertCore EDcert EDb9k

Log: `logs/cert_build.log`. All final runs RC 0 (D-files 138-199 s, C1 360 s, Core 19 s,
EDcert 6 s, EDb9k 5 s). Earlier RC 137 lines in the log are the OOM-killed attempts (old C0/C2).

## Axiom output
`#print axioms EDb9k.euler_1747_of_hprime_k` -> [propext, Classical.choice, Quot.sound]
(no `ofReduceBool`, no native_decide axiom). Sole hypothesis: `EDb8.HPrime`.

## File hashes (sha256 prefixes)
- EDcert.lean 275cd86edec2a865
- EDcertCore.lean fe967091dab2514c
- EDcertDefs.lean 14fe3d05f8709153
- EDb9k.lean 31549909514d6ee0

## Independent check
`finite_check.py`: sieve over 4,194,304 values, 0 uncovered, 43 candidates ending at 313.

## CI policy
EDcert modules are NOT in the lakefile or routine CI. Keep the build outside CI until a
runner with enough memory and time exists.

## Not claimed
`HPrime` (needs Weil -> Eichler-Shimura -> Igusa plus a Jacquet-Langlands/Eichler dictionary;
none in Mathlib). The bridge in HPRIME-STATEMENT-AND-BRIDGE.md is marked UNCHECKED.
