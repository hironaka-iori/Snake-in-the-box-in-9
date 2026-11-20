#!/bin/bash
# Every 2 h: write results/search_summary.txt from all Q9 192-search logs, validate >=190 snakes, commit+push.
cd "$(dirname $0)/.."
while true; do
  {
    echo "updated $(date -u)"
    echo "finished 10-min-or-longer runs and core-seconds:"
    grep -h END logs/cal1/*.txt logs/s192*/*.txt 2>/dev/null | awk '{split($5,a,"=");t+=a[2];n++} END{printf "runs=%d core_hours=%.1f\n",n,t/3600}'
    echo "best per finished fresh run (best_v = vertices):"
    grep -h END logs/cal1/*.txt logs/s192a/*.txt logs/s192b/*.txt logs/s192[c-z]/f*.txt 2>/dev/null | awk '{print $3}' | sort | uniq -c
    echo "bank-start runs improving beyond 191: $(grep -h BEST logs/s192*/bank*.txt 2>/dev/null | awk '$3!="edges=191"' | wc -l)"
    echo "any >=192 lines: $(grep -h 'edges=19[2-9]' logs/s192*/*.txt 2>/dev/null | wc -l)"
    cd src && python3 canon.py 190 ../logs/cal1/*.txt ../logs/s192a/*.txt ../logs/s192b/*.txt ../logs/s192[c-z]/f*.txt 2>&1 | tail -4; cd ..
  } > results/search_summary.txt
  git add results/search_summary.txt >/dev/null 2>&1 && git commit -qm "Milestone 40: periodic search summary" >/dev/null 2>&1 && { git fetch -q origin research/unconditional-241 && git merge -q --no-edit FETCH_HEAD; git push -q origin research/unconditional-241; } >/dev/null 2>&1
  sleep 7200
done
