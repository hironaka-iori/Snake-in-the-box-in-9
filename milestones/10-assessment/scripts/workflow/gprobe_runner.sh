#!/bin/bash
# gprobe_runner.sh N T PROBEFILE TIMEOUT OUT
W=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf
export PYTHONDONTWRITEBYTECODE=1
i=0
while read -r line; do
  w=$(echo $line | awk '{print $1}'); d=$(echo $line | awk '{print $2}')
  pre=$(echo $line | awk '{s=$3; for(i=4;i<=NF;i++) s=s","$i; print s}')
  out=$(timeout $4 $W/../venv/bin/python $W/global_sat2.py $1 $2 100000 cadical195 $pre 2>/dev/null)
  if [ -z "$out" ]; then echo "{\"index\":$i,\"weight\":$w,\"keep\":$d,\"status\":\"TIMEOUT\",\"seconds\":$4}"; else echo "$out" | sed "s/}\$/,\"index\":$i,\"weight\":$w,\"keep\":$d}/"; fi
  i=$((i+1))
done < $3 >> $5
