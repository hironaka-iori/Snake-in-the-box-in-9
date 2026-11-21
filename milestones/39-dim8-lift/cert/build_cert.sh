#!/bin/bash
# build one generated cube certificate: build_cert.sh OUTROOT MOD   (timings and peak RSS per module)
OUT=$1; MOD=$2; LB=${STACK:-$(cd "$(dirname "$0")/../lean/build" && pwd)}; L=/opt/lean-4.35.0-linux/bin/lean
cd $OUT/gen; mkdir -p $OUT/build; rm -f $MOD.lrat
for m in $(cat $MOD.modules); do
  mkdir -p $OUT/build/$(dirname $m); [ -f $OUT/build/$m.olean ] && continue   # resumable
  s=$(date +%s); LEAN_PATH=$OUT/build:$LB $L --root=. -o $OUT/build/$m.olean $m.lean > $OUT/b.out 2>&1 & P=$!; mx=0
  while kill -0 $P 2>/dev/null; do r=$(awk '/VmRSS/{print $2}' /proc/$P/status 2>/dev/null); [ -n "$r" ] && [ $r -gt $mx ] && mx=$r; sleep 1; done
  wait $P; rc=$?
  echo "$m rc=$rc $(( $(date +%s)-s )) s $((mx/1024)) MB $(grep -m2 -E 'error|axioms' $OUT/b.out | tr '\n' ' ')"
  [ $rc -ne 0 ] && { head -20 $OUT/b.out; exit 1; }
done
echo CERT BUILT
