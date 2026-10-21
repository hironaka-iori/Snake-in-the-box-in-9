"""Share-aware refinement rounds on the radius-4 L7k5K5 automaton.
Edge weight = s + max(T5(e), sum of single lower bounds of the 5 symbols)/(5*2M), T5(e) = proved lower bound on the
summed shareN (M=12) of the edge's 5-centre window (from threshold/ceiling/probe results).  Each round finds the
minimum-mean cycle and proves shareN >= T for its unknown 5-windows (threshold test).  usage: refine_share.py rounds T tl"""
import sys, json, os, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np
from automaton import load
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../10-window-aggregate/scripts'))
from refine import howard, key as rkey
M = 12
SINGLE_LO = {1: Fr(32, 120), 2: Fr(18, 120), 3: Fr(1, 24), 4: Fr(0), 5: Fr(0), 6: Fr(0)}

def known_lb():
    lb = {}
    def put(dirs, al, v):
        k = rkey(tuple(dirs), tuple(tuple(a) if isinstance(a, (list, tuple)) else (a, a) for a in al))
        lb[k] = max(lb.get(k, 0), v)
    for fn in ('threshold_results.jsonl', 'ceiling_results.jsonl', 'probe_results.jsonl', 'refshare_results.jsonl'):
        if not os.path.exists(fn): continue
        for l in open(fn):
            r = json.loads(l)
            if r.get('M', 12) != 12: continue
            al = r.get('alpha') or [((6, 21) if s == '6+' else (int(s), int(s))) for s in r['alpha_req'].split(',')]
            if len(r['dirs']) != 6: continue
            if 'result' in r:
                v = r['T'] if r['result'] == 'UNSAT' else 0
            elif r.get('status') == 'UNSAT_MODEL':
                v = 10 ** 6
            else:
                v = r.get('min_lower', 0)
            put(r['dirs'], al, v)
    return lb

def thr(arg):
    k, T, tl = arg
    from e1lib import ShareModel, wincert
    from pysat.card import ITotalizer
    from pysat.solvers import Cadical153
    dirs, al = list(k[0]), [a if a[0] != a[1] else a[0] for a in k[1]]
    sm = ShareModel(dirs, al, 4, M, tcap=T + 2); enc = sm.enc; t0 = time.time()
    tot = ITotalizer(lits=sm.ulits, ubound=T, top_id=enc.nv)
    res, wit = 'TIMEOUT', None
    with Cadical153(bootstrap_with=enc.clauses + tot.cnf.clauses) as s:
        # feasibility of the window itself first
        while time.time() - t0 < tl:
            s.conf_budget(20000); ok = s.solve_limited(assumptions=[-tot.rhs[T - 1]])
            if ok is None: continue
            if not ok:
                res = 'UNSAT'; break
            m = s.get_model(); sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = wincert.cycles_of(sel)
            if cyc:
                for cc in cyc: s.add_clause([-enc.var[w] for w in cc])
                continue
            per, _ = sm.share_of(sel); wit = sum(per.values()); res = 'SAT'; break
    return dict(dirs=dirs, alpha=[list(a) for a in k[1]], T=T, M=M, result=res, witness=wit, seconds=round(time.time() - t0, 1))

if __name__ == '__main__':
    rounds, T, tl = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    d = load(); W, U = d['W'], d['U']
    D = 5 * 2 * M * 120
    keys5 = [d['WIN'][e][3] for e in range(len(W))]
    syms5 = []
    for e in range(len(W)):
        a = d['inv'][int(U[e])][1]; syms5.append(tuple(a) + (int(W[e]),))
    for rnd in range(rounds):
        lb = known_lb()
        w = np.empty(len(W), dtype=np.int64)
        for e in range(len(W)):
            sl = sum(SINGLE_LO[s] for s in syms5[e])
            t5 = Fr(lb.get(keys5[e], 0), 2 * M)
            w[e] = int((int(W[e]) + max(t5, sl) / 5) * D)
        mu, cyc = howard(d['n'], d['U'], d['V'], w)
        lam = Fr(int(w[cyc].sum()), len(cyc) * D)
        todo = sorted({keys5[e] for e in cyc if keys5[e] not in lb})
        print(f'round {rnd}: mean {lam} = {float(lam):.4f} (v<= {9214/(35+float(lam)):.2f}) cycle {[int(W[e]) for e in cyc]} '
              f'known-on-cycle {sum(keys5[e] in lb for e in cyc)}/{len(cyc)} todo {len(todo)}', flush=True)
        if not todo: break
        with Pool(3) as p:
            res = p.map(thr, [(k, T, tl) for k in todo])
        with open('refshare_results.jsonl', 'a') as f:
            for r in res:
                f.write(json.dumps(r) + '\n'); print('   ', json.dumps(r), flush=True)
