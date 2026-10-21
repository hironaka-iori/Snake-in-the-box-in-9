"""Q9 = Q5 x Q4 in a palette, with one Q8 half (light bit 3 = 0) fixed to
a given Q8 palette snake (default: the Q8 record) and the other half free
(global SAT, milestone-20 Model2 with kept vertices)."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, json, time
sys.path.insert(0, _os.path.join(REPO, 'milestones/20-lower-bound-search/scripts'))
sys.path.insert(0, _os.path.join(REPO, 'milestones/21-snake-structure/scripts'))
from lns2 import Model2
from qmodel import check
from ptower import forbid
w = json.load(open(_os.path.join(REPO, 'outputs', 'snake8_witness.json')))['vertex_sequence']
L = [5, 2, 6]; H = [0, 1, 3, 4, 7]
cell = lambda v: sum(((v >> c) & 1) << i for i, c in enumerate(L))
hv = lambda v: sum(((v >> c) & 1) << i for i, c in enumerate(H))
REC = [hv(v) | (cell(v) << 5) for v in w]
A = [0, 1, 2, 6, 19, 20, 21, 23, 24]; B = [4, 5, 7, 12, 16, 17, 18, 25]
if __name__ == '__main__':
    T = int(sys.argv[1]); tl = float(sys.argv[2]); cut = [int(a) for a in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0, 0]
    pal = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    keep = REC[cut[0]:len(REC) - cut[1]]
    assert check(REC, 8)
    bad = set(forbid(5, 4, A, B)) if pal else set(); assert not (bad & set(keep))
    m = Model2(set(keep), T, forbid=sorted(bad), solver='cadical195')
    t = time.time(); r, p = m.run(time_budget=tl)
    rec = dict(kind='halfkeep', palette=pal, cut=cut, kept=len(keep), target=T, free=len(m.free), result=r, secs=round(time.time() - t, 1), cuts=m.cuts)
    if p: rec['length'] = len(p); rec['valid'] = check(p, 9); rec['path'] = p
    print(json.dumps({a: b for a, b in rec.items() if a != 'path'}), flush=True)
    open('halfkeep.jsonl', 'a').write(json.dumps(rec) + '\n')
