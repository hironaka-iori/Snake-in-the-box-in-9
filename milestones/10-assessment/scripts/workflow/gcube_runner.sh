#!/bin/bash
# gcube_runner.sh N T CUBEFILE TIMEOUT STEP OFFSET OUT   (runs every STEP-th cube starting at OFFSET)
W=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf
export PYTHONDONTWRITEBYTECODE=1
i=0
while read -r pre; do
  if [ $(( (i - $6) % $5 )) -eq 0 ] && [ $i -ge $6 ]; then
    t0=$(date +%s.%N)
    out=$(timeout $4 $W/../venv/bin/python $W/global_sat2.py $1 $2 100000 cadical195 $pre 2>/dev/null)
    t1=$(date +%s.%N)
    if [ -z "$out" ]; then echo "{\"index\":$i,\"status\":\"TIMEOUT\",\"wall\":$4}"; else echo "$out" | sed "s/}\$/,\"index\":$i,\"wall\":$(printf "%.3f" $(echo "$t1 - $t0" | bc))}/"; fi
  fi
  i=$((i+1))
done < $3 >> $7
