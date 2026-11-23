# Closure-audit evidence for commit 0bf5a18 (HPrime chain)

Produced 2026-11-23 (UTC) by `run-readonly.sh` (steps 0-3 only, BUILD=0). It reads the Lean text with `git show 0bf5a18:<path>`; it writes nothing in the repo.

What these files show: the exact statements of `HPrime`, `Tn`, `U`, `Tl`, `oneY`, `chiE`, `chiY`, `Tn_adj`, `Adm`, `WeakAt`, `HWeak`, `EDb9.euler_1747_of_hprime`, `Section83.H31gt3` as they stand at 0bf5a18, and a text count of `sorry` / `admit` / `native_decide` / `axiom` per file of the euler-weak chain.

What they do NOT show: any Lean build or `#print axioms` output. `lean` and `lake` were not installed where this ran (see STEP 0 in the report), so there is no kernel check here. The text counts include comments (the two `sorry` hits are the words "no sorry" in comments). The kernel evidence for HPrime => HWeak => H31gt3 is CI run #1 at 0bf5a18, not these files.

Note: `euler/StageA4o.lean` etc. listed as untracked in the report are stray copies outside `euler/lean/EulerLean/`; the audit read only the committed tree.

Files: `report-steps0-3.txt` (full output), `grep_full.txt` (every matching line, large), `run-readonly.sh` (the script; set REPO if the repo is not at ~/Desktop/DM3-lab).
