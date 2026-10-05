#!/usr/bin/env bash
# Check project files in order in the REPL, each in the environment produced by the previous one.
# usage: scripts/chaincheck.sh <start-env> file1.lean file2.lean ...
env=$1; shift
for f in "$@"; do
  out=$(python scripts/leanrepl.py check "$f" --env "$env" 2>&1)
  last=$(echo "$out" | tail -1)
  echo "== $f: $last"
  if echo "$last" | grep -q "(0 errors"; then
    env=$(echo "$last" | awk '{print $2}')
    echo "$out" | grep "^sorry at" | cut -c1-80
  else
    echo "$out" | grep -v "^inst\|^E :\|^H :\|^I :\|^M :" | head -60
    exit 1
  fi
done
echo "final env $env"
