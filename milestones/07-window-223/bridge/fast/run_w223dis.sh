#!/bin/bash
# Reproduce the W223Dis FastRup benchmark (one Lean process at a time, nice 10, RSS watchdog 2.9 GB).
# Needs data/w223_dis.cnf and data/w223_dis.lrat (milestones/07-window-223/bridge/gen2.py, or drat-trim -L).
set -e
cd "$(dirname "$0")"
./lc.py WinCNF.lean FastRup.lean FastRupCmd.lean
python3 -I gen_fast.py ../data/w223_dis.cnf ../data/w223_dis.lrat FDis W223Dis > fdis.list
python3 bench.py "FastRup W223Dis" $(cat fdis.list)
printf 'import FDis.Main\n#print axioms W223Dis_unsat\n' > Ax.lean && ./lc.py Ax.lean && cat Ax.lean.out
