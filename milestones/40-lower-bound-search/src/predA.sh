#!/bin/bash
# Cross-dimension calibration: identical annealer config in Q7, Q8 (one core).
out=logs/predA; mkdir -p $out
CFG="-b 4 -T0 0.65 -T1 0.65"
for s in $(seq 1 40); do bin/surgery -n 7 -s $s -steps 100000000000 -t 20 -r 40 $CFG -o $out/q7_s$s.txt; done
for s in $(seq 1 30); do bin/surgery -n 8 -s $s -steps 100000000000 -t 120 -r 85 $CFG -o $out/q8_s$s.txt; done
echo DONE > $out/DONE
