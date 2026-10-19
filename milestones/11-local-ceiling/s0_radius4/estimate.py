"""Non-rigorous estimate: automaton mean when every untested 5-window is assumed to force shareN >= F (M=12).
Tested windows use the proved bound (UNSAT at T) or the witness value when SAT (optimistic), and the threshold T on TIMEOUT."""
import sys, json, os
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
from automaton import load
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../10-window-aggregate/scripts'))
from refine import howard, key as rkey
from refine_share import SINGLE_LO, M
val = {}
for fn in ('threshold_results.jsonl', 'ceiling_results.jsonl', 'probe_results.jsonl', 'refshare_results.jsonl'):
    for l in open(fn):
        r = json.loads(l)
        if len(r['dirs']) != 6: continue
        al = r.get('alpha') or [((6, 21) if s == '6+' else (int(s), int(s))) for s in r['alpha_req'].split(',')]
        k = rkey(tuple(r['dirs']), tuple(tuple(a) for a in al))
        if 'result' in r:
            v = r['T'] if r['result'] in ('UNSAT', 'TIMEOUT') else r['witness']
        elif r.get('status') == 'UNSAT_MODEL':
            v = 10 ** 4
        else:
            v = r['witness_share'] if r['status'] != 'OPT' else r['min_lower']
        val[k] = max(val.get(k, 0), v) if k in val and 'result' in r and r['result'] == 'UNSAT' else min(val.get(k, 10 ** 5), v) if k in val else v
d = load(); W, U = d['W'], d['U']
D = 5 * 2 * M * 120
keys5 = [d['WIN'][e][3] for e in range(len(W))]
for F in [int(x) for x in sys.argv[1].split(',')]:
    w = np.array([int((int(W[e]) + Fr(min(val.get(keys5[e], F), 2000), 2 * M) / 5) * D) for e in range(len(W))], dtype=np.int64)
    mu, cyc = howard(d['n'], d['U'], d['V'], w)
    lam = Fr(int(w[cyc].sum()), len(cyc) * D)
    print(json.dumps({'F': F, 'F_per_vertex': F / 120, 'mean': float(lam), 'v_le': 9214 / (35 + float(lam)),
                      'cycle': [int(W[e]) for e in cyc], 'tested_on_cycle': sum(keys5[e] in val for e in cyc), 'len': len(cyc)}), flush=True)
if len(sys.argv) > 2:   # dump the F-cycle windows and test them at threshold T2
    from multiprocessing import Pool
    from refine_share import thr
    T2 = int(sys.argv[2])
    ks = sorted({keys5[e] for e in cyc})
    todo = [(k, T2 if val.get(k, 0) >= 108 else 108, 60) for k in ks if val.get(k, 0) < T2]
    print('testing', len(todo), 'windows', flush=True)
    with Pool(3) as p:
        res = p.map(thr, todo)
    with open('refshare_results.jsonl', 'a') as f:
        for r in res:
            f.write(json.dumps(r) + '\n'); print('   ', json.dumps(r), flush=True)
