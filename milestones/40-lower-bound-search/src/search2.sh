#!/bin/bash
# 192 search, 3 parallel jobs of 600 s: two fresh-start configs + one start from a bank 191 snake.
out=logs/s192c; mkdir -p $out; BIN=bin/surgery
for k in $(seq 1 3000); do
  s=$((300000+k))
  case $((k%3)) in
    0) echo "$BIN -s $s -steps 100000000000 -t 600 -r 189 -b 4 -T0 0.65 -T1 0.65 -o $out/fa_$k.txt";;
    1) echo "$BIN -s $s -steps 100000000000 -t 600 -r 189 -b 5 -T0 0.9 -T1 0.9 -o $out/fb_$k.txt";;
    2) b=$(printf %03d $((k/3%131))); echo "$BIN -s $s -steps 100000000000 -t 600 -r 190 -b 4 -T0 0.65 -T1 0.65 -init data/bankinit/b$b.txt -o $out/bank${b}_$k.txt";;
  esac
done | xargs -P 3 -I{} sh -c '{}'
