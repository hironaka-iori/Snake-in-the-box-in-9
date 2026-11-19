#!/bin/bash
# Lower bounds on h_{n,k}(1) by annealing: max degree<=2 induced sets, <=1 path, every cycle spans > k directions.
out=../data/h_table_raw.txt
run(){ n=$1; k=$2; it=$3; for s in 1 2 3; do /tmp/fake_sa $n 1 $k $it $s | head -1 | sed "s/^/seed=$s it=$it /" >> $out; done; }
export -f run; export out
{ for k in 4 5 6 7; do echo "7 $k 100000000"; done
  for k in 4 5 6 7 8; do echo "8 $k 300000000"; done
  for k in 4 5 6 7 8 9; do echo "9 $k 800000000"; done; } | xargs -P 3 -L 1 bash -c 'run $0 $1 $2'
