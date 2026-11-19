#!/bin/bash
# kernel-check the cover tables (decide +kernel per chunk) and build Final229 (lean/gen)
cd "$(dirname "$0")/../lean"
for m in $(cat gen/checks.txt); do
  [ -f build/$m.olean ] && continue
  s=$(date +%s)
  out=$(LEAN_PATH=build nice -n 5 /opt/lean-4.35.0-linux/bin/lean -o build/$m.olean gen/$m.lean 2>&1)
  echo "$m $(( $(date +%s)-s )) s $(echo "$out" | grep -E -m2 'error|axioms')"
done
echo CHECKS DONE
