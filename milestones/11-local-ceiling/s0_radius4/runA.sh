#!/bin/bash
# single-centre minima, one process per instance, hard timeout 560 s each
ulimit -v 2500000
cd "$(dirname "$0")"
for spec in "12 3" "12 4" "12 5" "12 6+" "60 1" "60 2" "60 3" "60 4" "60 5" "60 6+"; do
  set -- $spec
  avail=$(free -g | awk '/Mem:/{print $7}')
  if [ "$avail" -lt 4 ]; then echo "SKIP $spec low mem $avail"; continue; fi
  echo "=== M=$1 alpha=$2 $(date +%T)"
  OPENBLAS_NUM_THREADS=1 timeout 560 nice -n 19 python3 single.py $1 4 $2 520 $(( $1 * 2 ))
  echo "=== exit $?"
done
