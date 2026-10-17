#!/bin/bash
W=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf
e=$1
for K in 128 120 112 104 96 88 80 72 64 56 48 40 32 24 16 8 4 2; do
  $W/knuth est 9 193 50000 $((K*7+1)) 0 $K < $W/prefixes/pre_$e.txt | python3 -c "
import json,sys; d=json.loads(sys.stdin.read()); print(json.dumps(dict(entry='$e',keep=d['keep'],mean=d['mean'],se=d['se'],max_share=d['max_share'],maxdepth=d['maxdepth'])))"
done
