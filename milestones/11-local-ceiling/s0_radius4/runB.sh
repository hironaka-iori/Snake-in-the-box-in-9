#!/bin/bash
ulimit -v 2500000
cd "$(dirname "$0")"
M=${M:-12}
while read dirs al; do
  avail=$(free -g | awk '/Mem:/{print $7}')
  if [ "$avail" -lt 4 ]; then echo "SKIP $dirs $al low mem $avail"; continue; fi
  echo "=== $dirs $al $(date +%T)"
  OPENBLAS_NUM_THREADS=1 timeout ${TO:-400} nice -n 19 python3 window.py $M 4 $dirs $al ${TL:-360}
  echo "=== exit $?"
done < "$1"
