#!/bin/bash
for V in 64 62 60 58 56 54 52; do timeout 4000 python3 snake_sat.py 7 $V 3600 >> ../data/sat_global.txt 2>&1; done
