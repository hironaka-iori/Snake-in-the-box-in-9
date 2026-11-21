#!/bin/bash
# Fleet search for a >=192-edge snake in Q9. Runs JOBS (default 4) parallel workers forever.
# usage (from anywhere):  milestones/40-lower-bound-search/src/fleet.sh VARIANT MACHINE_INDEX [JOBS]
#   VARIANT: sym    symmetry-restricted annealing (random involution of Q9 per run, src/sym.c)
#            q8     surgery annealing started from two Q8 snakes glued across a facet
#            window CP-SAT exact window repair (60-130 vertices) of the 131 bank 191-snakes
#            plain  plain surgery annealing (fresh starts), the baseline method
# Logs: logs/fleet/VARIANT_MACHINE/ ; any snake >= 192 edges is re-validated with the
# independent checker src/check.py and written to logs/fleet/FOUND192.txt and stdout.
set -u
cd "$(dirname "$0")/.."
VAR=$1; M=$2; JOBS=${3:-4}
OUT=logs/fleet/${VAR}_$M; mkdir -p $OUT bin
[ -x bin/surgery ] || gcc -O3 -march=native -o bin/surgery src/surgery.c -lm
[ -x bin/sym ] || gcc -O3 -march=native -o bin/sym src/sym.c -lm
if [ "$VAR" = window ]; then python3 -c "import ortools" 2>/dev/null || pip install -q ortools; fi

found() {  # $1 = log file
  if grep -q "edges=19[2-9]\|edges=2[0-9][0-9]" "$1"; then
    r=$(python3 src/check.py 9 "$1" | grep -E "edges=(19[2-9]|2[0-9][0-9]) OK")
    if [ -n "$r" ]; then
      { echo "=== $(date -u) $VAR machine $M file $1"; echo "checker: $r";
        grep -E "edges=(19[2-9]|2[0-9][0-9])" "$1"; } | tee -a logs/fleet/FOUND192.txt
    fi
  fi
}

worker() {
  j=$1
  for k in $(seq 1 1000000); do
    s=$(( (M*10 + j) * 1000000 + k ))
    f=$OUT/w${j}_$k.txt
    case $VAR in
      sym)   bin/sym -n 9 -s $s -t 600 -r 188 -b $((4 + k%2)) -T 0.$((65 + 25*(k%2))) -o $f ;;
      q8)    python3 src/q8prime.py $s $OUT/init_$j.txt > /dev/null &&
             bin/surgery -s $s -steps 100000000000 -t 600 -r 189 -b 4 -T0 0.65 -T1 0.65 -init $OUT/init_$j.txt -o $f ;;
      window) (cd src && python3 window_repair.py 9 "../data/bankinit/*.txt" "../$OUT/w*.txt" -min 190 \
               -t 3600 -s $s -wmin 60 -wmax 130 -tl 600 -o ../$f) ;;
      plain) bin/surgery -s $s -steps 100000000000 -t 600 -r 189 -b $((4 + k%2)) -T0 0.$((65 + 25*(k%2))) -T1 0.$((65 + 25*(k%2))) -o $f ;;
      *) echo "unknown variant $VAR"; exit 1 ;;
    esac
    found $f
  done
}
echo "fleet $VAR machine $M jobs $JOBS started $(date -u), logs in $OUT"
for j in $(seq 0 $((JOBS-1))); do worker $j & done
wait
