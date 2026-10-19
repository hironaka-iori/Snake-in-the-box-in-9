"""Minimum total shareN (sum over all centres) for one window. usage: window.py M radius dirs alphas tl [Kmax]
alphas like 2,6+,4 ; dirs like 0,1,2,3"""
import sys, json
from e1lib import ShareModel
M = int(sys.argv[1]); radius = int(sys.argv[2])
dirs = [int(x) for x in sys.argv[3].split(',')]
al = [(6, 21) if s == '6+' else int(s) for s in sys.argv[4].split(',')]
tl = float(sys.argv[5]); Kmax = int(sys.argv[6]) if len(sys.argv) > 6 else 2 * M * len(al)
sm = ShareModel(dirs, al, radius, M, tcap=Kmax + 2)
print(f'M={M} r={radius} dirs={dirs} alphas={al}: vars {sm.enc.nv} ulits {len(sm.ulits)}', flush=True)
r = sm.minimise2(Kmax=Kmax, time_limit=tl, log=lambda x: print(x, flush=True))
r.update(M=M, radius=radius, dirs=dirs, alpha_req=sys.argv[4])
print(json.dumps({k: v for k, v in r.items() if k != 'sel'}), flush=True)
with open('windows_results.jsonl', 'a') as f:
    f.write(json.dumps(r) + '\n')
