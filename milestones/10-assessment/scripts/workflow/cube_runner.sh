#!/bin/bash
# cube_runner.sh PREFIXFILE TIMEOUT START COUNT OUT
W=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf
export PYTHONDONTWRITEBYTECODE=1
for ((i=$3; i<$3+$4; i++)); do
  line=$(sed -n "$((i+1))p" $1); [ -z "$line" ] && break
  w=$(echo $line | awk '{print $1}'); d=$(echo $line | awk '{print $2}')
  out=$(timeout $2 $W/../venv/bin/python $W/sat_cube.py $1 100000 193 $i 1 2>/dev/null)
  if [ -z "$out" ]; then echo "{\"tag\":\"probe\",\"weight\":$w,\"keep\":$d,\"status\":\"TIMEOUT\",\"seconds\":$2,\"index\":$i}"; else echo "$out" | sed "s/}\$/,\"index\":$i}/"; fi
done >> $5
