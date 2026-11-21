#!/bin/bash
export PATH=$HOME/.elan/bin:$PATH
cd /home/claude/lean-audit
LP=$(lake env printenv LEAN_PATH):/home/claude/lean-audit/ol:/home/claude/lean-audit/ed
for f in "$@"; do
  s=$(date +%s)
  LEAN_PATH=$LP lean -R ed -o ed/$f.olean ed/$f.lean > ed/$f.out 2>&1
  echo "$f RC $? SECS $(( $(date +%s)-s ))" >> ed/build.log
done
