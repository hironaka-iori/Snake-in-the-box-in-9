"""Ceiling: share witnesses of the 5-centre (and 3-centre) windows on the 42/11 minimum cycle of the
radius-4 automaton.  Any proof using window-minimum shares on this cycle can add at most
(1/len)*sum_e witness_e/c per vertex.  usage: ceiling.py c tl"""
import sys, json
from fractions import Fraction as Fr
from e1lib import ShareModel
c = int(sys.argv[1]); tl = float(sys.argv[2]); src = sys.argv[3]; Kmax = int(sys.argv[4])
base = json.load(open(src))
M = 12
out = []
for i, wins in enumerate(base['cycle_windows']):
    k = wins[c - 2]
    dirs = k[0]; al = [tuple(a) if a[0] != a[1] else a[0] for a in k[1]]
    sm = ShareModel(dirs, al, 4, M, tcap=Kmax + 2)
    r = sm.minimise2(Kmax=Kmax, time_limit=tl, budget=30000)
    r.pop('sel', None)
    r.update(dirs=dirs, alpha=k[1], edge=i, src=src, c=c, M=M)
    with open('ceiling_results.jsonl', 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps(r), flush=True)
    out.append(r)
json.dump(out, open(f'ceiling_c{c}_{src}', 'w'))
