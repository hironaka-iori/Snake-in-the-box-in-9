#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 prepare.py
c++ -O3 -std=c++17 forest.cpp -o search
c++ -O3 -std=c++17 exact.cpp -o exact
run(){ name=$1; shift; ./search "$@" < inputs.txt > "$name.log"; }
run seven 0 45000 3500 192 140
run archive 1 1500 750 192 141
run controls 2 3 3500 190 142
run short 0 6500 650 190 143
run warp7odd 3 60000 3000 192 230
run warp191odd 4 6000 1500 192 233
run warp7even 5 60000 3000 192 232
run warp191even 6 6000 1500 192 235
run sevenodd 7 60000 3500 192 240
run archiveodd 8 3000 1000 192 241
run hardcontrol 9 2 8000 190 248
run archive191 1 300 1200 191 246
run archive190 1 300 1200 190 245
run perm7e 10 140000 2000 192 301
run perm191e 11 5000 1000 192 302
run perm7o 12 140000 2000 192 303
run perm191o 13 5000 1000 192 304
./exact 0 0 <inputs.txt >exact7e.log
./exact 0 2 <inputs.txt >exact7o.log
./exact 1 0 <inputs.txt >exact191e.log
./exact 1 2 <inputs.txt >exact191o.log
python3 audit.py >audit.json
