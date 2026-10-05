#!/usr/bin/env bash
# Compile project files one at a time to .olean (as lake build would), stopping at the first error.
# usage: scripts/compile1.sh ShortTime/Linear/Foo.lean ...
for f in "$@"; do
  m=${f%.lean}
  mkdir -p ".lake/build/lib/lean/$(dirname "$m")"
  start=$(date +%s)
  out=$(LEAN_NUM_THREADS=2 lake env lean -o ".lake/build/lib/lean/$m.olean" -i ".lake/build/lib/lean/$m.ilean" "$f" 2>&1)
  code=$?
  echo "== $f: exit $code ($(( $(date +%s) - start ))s)"
  echo "$out" | grep -E "error|declaration uses 'sorry'|declaration uses \`sorry\`" | head -20
  if [ $code -ne 0 ]; then echo "$out" | grep -v "^warning" | head -40; exit 1; fi
done
exit 0
