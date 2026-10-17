#!/bin/bash
W=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf
K=$1
for f in $W/prefixes/pre_*.txt; do
  e=$(basename $f .txt)
  $W/knuth est 9 193 3000 $((K*13+7)) 0 $K < $f | python3 -c "
import json,sys; d=json.loads(sys.stdin.read()); print(json.dumps(dict(entry='$e',keep=$K,mean=d['mean'],se=d['se'])))"
done
