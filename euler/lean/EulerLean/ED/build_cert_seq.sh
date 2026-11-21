#!/bin/bash
# Sequential build (each file grows to ~5 GB; parallel builds were OOM-killed).  Chunk files D0..D13 (16 chunks each) plus the already-built C1 (chunks 32-63).
export PATH=$HOME/.elan/bin:$PATH
cd /home/claude/lean-audit
LP=$(lake env printenv LEAN_PATH):/home/claude/lean-audit/ol:/home/claude/lean-audit/ed
b() { s=$(date +%s); LEAN_PATH=$LP lean -R ed -o ed/$1.olean ed/$1.lean > ed/$1.out 2>&1; echo "$1 RC $? SECS $(( $(date +%s)-s ))" >> ed/cert.log; }
for n in "$@"; do b $n; done
