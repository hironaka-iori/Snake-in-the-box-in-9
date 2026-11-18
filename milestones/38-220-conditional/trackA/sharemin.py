"""CP-SAT search for 7-centre local models of low corner share (counts free), hinted with the lowest-share
validated witness of the shape from trackB/data/witness_W24.jsonl.  Truth check of the uniform share levels:
a validated model of share S caps every uniform floor at X <= S.
usage: sharemin.py OUT.jsonl tl workers [nshapes]"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'trackB')); sys.path.insert(0, HERE)
import tier7
from tier7 import ws, window_from_dirs
from cpmin import minimize
from sawit import check
out, tl, nw = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
n = int(sys.argv[4]) if len(sys.argv) > 4 else 5
best = {}
for l in open(os.path.join(HERE, '..', 'trackB', 'data', 'witness_W24.jsonl')):
    r = json.loads(l); w = window_from_dirs(list(r['dirs'])); sh = ws.share_exact(w, r['sel'])
    if tuple(r['dirs']) not in best or sh < best[tuple(r['dirs'])][0]:
        best[tuple(r['dirs'])] = (sh, r['sel'])
for dirs, (sh, sel) in sorted(best.items(), key=lambda x: x[1][0])[:n]:
    r = minimize(list(dirs), wA=0, tl=tl, workers=nw, hint=set(sel))
    r['seed_share'] = sh
    if 'sel' in r:
        r['valid_cnf'] = bool(check(window_from_dirs(list(dirs)), r['sel']))
        r['share_exact'] = ws.share_exact(window_from_dirs(list(dirs)), r['sel'])
    open(out, 'a').write(json.dumps(r) + '\n')
    print({k: v for k, v in r.items() if k != 'sel'}, flush=True)
