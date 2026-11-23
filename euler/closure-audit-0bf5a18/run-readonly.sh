#!/bin/bash
# Closure-audit evidence for commit 0bf5a18. READ-ONLY on the repo.
REPO="${REPO:-$HOME/Desktop/DM3-lab}"
C=0bf5a18
OUT=/tmp/closure-audit
R="$OUT/report.txt"
BUILD="${BUILD:-1}"
: > "$R"
log(){ printf '%s\n' "$*" | tee -a "$R"; }
sec(){ log ""; log "===== $* ====="; }
run(){ "$@" 2>&1 | tee -a "$R"; }
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
L=euler/lean/EulerLean
FILES="$L/ED/EDb8.lean $L/StageA4o.lean $L/EDweak/EDweak.lean $L/ED/EDb9.lean"
CHAIN="StageA4o EDa1 EDa3 EDa4 EDa5 EDa6 EDa7 EDa8 EDa9 EDb1 EDb2 EDb3 EDb4 EDb5 EDb6 Stage83cut EDb7 EDb8 EDb9 EDweak"
NAMES='HPrime|Tn|Tl|chiE|oneY|Tl_one_eig|Tl_chi_eig|Tl_symm|Tn_adj|HWeak|H31gt3'
sec "STEP 0: environment"
run date; run uname -a
log "lean: $(command -v lean || echo NOT FOUND)  lake: $(command -v lake || echo NOT FOUND)"
cd "$REPO" 2>/dev/null || { log "REPO NOT FOUND at $REPO"; exit 1; }
sec "STEP 1: commit identity and working tree (read-only git)"
if ! git cat-file -e "$C^{commit}" 2>/dev/null; then log "COMMIT $C NOT PRESENT LOCALLY."; exit 1; fi
run git rev-parse "$C^{commit}"
run git log -1 --format=fuller "$C"
log "--- HEAD:"; run git rev-parse HEAD
log "--- commits after $C (max 30):"; run git log --oneline "$C..HEAD" | head -30
log "--- Lean files changed between $C and HEAD:"; run git diff --stat "$C" HEAD -- euler/lean
log "--- git status --short:"; run git status --short
sec "STEP 2: definitions and statements at $C (git show; full grep in grep_full.txt)"
: > "$OUT/grep_full.txt"
for f in $FILES; do
  echo "### $f" >> "$OUT/grep_full.txt"
  git show "$C:$f" | grep -n -E -w "$NAMES" >> "$OUT/grep_full.txt"
  log "--- $f : matching lines = $(git show "$C:$f" | grep -c -E -w "$NAMES")"
  log "--- declarations mentioning the names:"
  git show "$C:$f" | grep -n -E "^[[:space:]]*(noncomputable |private |protected )*(def|theorem|lemma|abbrev)[[:space:]]+[A-Za-z0-9_.']*($NAMES)" | tee -a "$R"
done
log "--- full text of key declarations (up to 25 lines each):"
for spec in "$L/ED/EDb8.lean:def HPrime" "$L/StageA4o.lean:def Tn " "$L/StageA4o.lean:def U (n" "$L/StageA4o.lean:theorem U_mk" \
            "$L/StageA4o.lean:def Tl " "$L/StageA4o.lean:def oneY" "$L/StageA4o.lean:def chiE" "$L/StageA4o.lean:def chiY" \
            "$L/StageA4o.lean:theorem Tl_one_eig" "$L/StageA4o.lean:theorem Tn_adj" "$L/StageA4o.lean:def Adm" \
            "$L/EDweak/EDweak.lean:def WeakAt" "$L/EDweak/EDweak.lean:def HWeak" "$L/ED/EDb9.lean:theorem euler_1747_of_hprime"; do
  f="${spec%%:*}"; pat="${spec#*:}"
  log "### $f :: $pat"
  git show "$C:$f" | awk -v p="$pat" 'index($0,p){on=1;n=0} on{print NR": "$0; n++; if(n>=25 || (n>1 && $0 ~ /^[[:space:]]*$/)) on=0}' | head -60 | tee -a "$R"
done
sec "STEP 2b: Section83.H31gt3 statement at $C"
git show "$C:$L/ED/Stage83cut.lean" | awk 'index($0,"def H31gt3"){on=1;n=0} on{print NR": "$0; n++; if(n>=8) on=0}' | tee -a "$R"
sec "STEP 3: sorry / admit / axiom / native_decide / implemented_by at $C (text search, includes comments)"
for m in $CHAIN; do
  case "$m" in StageA4o) f="$L/StageA4o.lean";; EDweak) f="$L/EDweak/EDweak.lean";; *) f="$L/ED/$m.lean";; esac
  t="$(git show "$C:$f" 2>/dev/null)" || { log "$m : FILE MISSING at $C"; continue; }
  s=$(printf '%s\n' "$t" | grep -c -w sorry); a=$(printf '%s\n' "$t" | grep -c -w admit)
  nd=$(printf '%s\n' "$t" | grep -c native_decide); ib=$(printf '%s\n' "$t" | grep -c -E 'implemented_by|@\[extern')
  log "$m : sorry=$s admit=$a native_decide=$nd implemented_by/extern=$ib"
  printf '%s\n' "$t" | grep -n -E "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private |protected )*(axiom|opaque)[[:space:]]" | sed "s|^|   AXIOM/OPAQUE in $m: |" | tee -a "$R"
  [ "$s" != "0" ] && printf '%s\n' "$t" | grep -n -w sorry | sed "s|^|   sorry-line in $m: |" | tee -a "$R"
done
sec "STEP 4 SKIPPED (BUILD=0): no kernel check."
sec "DONE. Report at $R"
