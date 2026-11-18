#!/bin/bash
# Independent-kernel check of the 4.35 assembly (milestone 36): for every module of MODLIST (glue chunks,
# top module, final module), export its closure with exportiface.lean (certificates public-only: their
# `refuted` theorems become assumptions), then check the export with nanoda_bin (independent Rust kernel,
# every assumption listed explicitly in permitted_axioms) and with `leanchecker --from-export`.
# usage (from any directory; writes exp<TAG>/ and OUT there):
#   xkernel435.sh TAG IFACE GLUEBUILD CHAINBUILD FINALDIR MODLIST OUT
R=$(cd "$(dirname "$0")/../.." && pwd)
T=$1; IF=$2; GB=$3; CB=$4; FD=$5; ML=$6; OUT=$7
export PATH=/opt/lean-4.35.0-linux/bin:$PATH; L=/root/l435
P=$(ls -d $L/mathlib4/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':')
export IFACE=$IF LEAN_PATH=$FD:$L/prod/core:$CB:$L/floors/build:$GB:$IF:$L/mathlib4/.lake/build/lib/lean:$P
mkdir -p exp$T; touch $OUT
while read m; do
  grep -q " $m " $OUT && continue
  e=exp$T/$m.json
  t0=$(date +%s.%N)
  lean --run $R/lean435/tools/exportiface.lean $m 2> exp$T/$m.err | sed -n '/^{"meta"/,$p' > $e
  if [ ! -s $e ]; then echo "EXPORTFAIL $m $(head -c 200 exp$T/$m.err | tr '\n' ' ')" >> $OUT; continue; fi
  python3 $R/lean435/tools/nanocfg435.py $e > /dev/null
  nd=$(grep -c '"thm"\|"def"\|"induct"\|"axiom"\|"opaque"' $e)
  nanoda_bin $e.nanoda.json > $e.nanoda.out 2>&1; rn=$?
  leanchecker --from-export $e > $e.lc.out 2>&1; rl=$?
  na=$(wc -l < $e.axioms.txt); nc=$(grep -o "Checked [0-9]* declarations" $e.nanoda.out | grep -o "[0-9]*")
  echo "R $m nanoda=$rn leanchecker=$rl decls=$nc axioms=$na axsha=$(sha256sum < $e.axioms.txt | cut -c1-16) $(echo "$(date +%s.%N)-$t0" | bc)" >> $OUT
  rm -f $e
done < $ML
echo DONE >> $OUT
