#!/bin/bash
# usage: portfolio.sh OUTDIR TLIMIT "config1" "config2" ...   (each config run once per seed, one job per core)
# env SEEDS (default "1 2"), JOBS (default 4)
out=$1; tl=$2; shift 2; mkdir -p $out
BIN=$(dirname $0)/../bin/surgery
jobs=()
for seed in ${SEEDS:-1 2}; do i=0; for cfg in "$@"; do i=$((i+1)); jobs+=("$BIN -s $(( ${SEED0:-0} + seed*100+i)) -steps 100000000000 -t $tl -r 189 $cfg -o $out/c${i}_s${seed}.txt"); done; done
printf '%s\n' "${jobs[@]}" > $out/jobs.txt
printf '%s\n' "${jobs[@]}" | xargs -P ${JOBS:-4} -I{} sh -c '{}'
echo DONE > $out/DONE
