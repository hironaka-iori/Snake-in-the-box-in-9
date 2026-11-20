#!/bin/bash
# usage: search4.sh OUTDIR SEEDBASE JOBS : 600 s runs cycling fresh(b4,T.65), fresh(b5,T.9), bank-start.
out=$1; base=$2; P=$3; mkdir -p $out; BIN=bin/surgery
for k in $(seq 1 100000); do
  s=$((base+k))
  case $((k%3)) in
    0) echo "$BIN -s $s -steps 100000000000 -t 600 -r 189 -b 4 -T0 0.65 -T1 0.65 -o $out/fa_$k.txt";;
    1) echo "$BIN -s $s -steps 100000000000 -t 600 -r 189 -b 5 -T0 0.9 -T1 0.9 -o $out/fb_$k.txt";;
    2) b=$(printf %03d $((k/3%131))); echo "$BIN -s $s -steps 100000000000 -t 600 -r 190 -b 4 -T0 0.65 -T1 0.65 -init data/bankinit/b$b.txt -o $out/bank${b}_$k.txt";;
  esac
done | xargs -P $P -I{} sh -c '{}'
