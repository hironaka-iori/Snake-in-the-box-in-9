"""Prove shareN >= T (M=12) for 5-centre windows on a cycle: UNSAT of (model & shareN <= T-1).
usage: threshold.py src.json T tl edges(comma list)"""
import sys, json, time
from e1lib import ShareModel, wincert
from pysat.card import ITotalizer
from pysat.solvers import Cadical153
src, T, tl = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
edges = [int(x) for x in sys.argv[4].split(',')]
base = json.load(open(src)); M = 12; c = 5
for i in edges:
    k = base['cycle_windows'][i][c - 2]
    al = [tuple(a) if a[0] != a[1] else a[0] for a in k[1]]
    sm = ShareModel(k[0], al, 4, M, tcap=T + 2)
    enc = sm.enc; t0 = time.time()
    tot = ITotalizer(lits=sm.ulits, ubound=T, top_id=enc.nv)
    res = 'TIMEOUT'; wit = None; cuts = 0
    with Cadical153(bootstrap_with=enc.clauses + tot.cnf.clauses) as s:
        while time.time() - t0 < tl:
            s.conf_budget(30000)
            ok = s.solve_limited(assumptions=[-tot.rhs[T - 1]])
            if ok is None: continue
            if not ok: res = 'UNSAT'; break
            m = s.get_model(); sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = wincert.cycles_of(sel)
            if cyc:
                for cc in cyc: s.add_clause([-enc.var[w] for w in cc]); cuts += 1
                continue
            per, rat = sm.share_of(sel); wit = sum(per.values()); res = 'SAT'; break
    r = dict(src=src, edge=i, dirs=k[0], alpha=k[1], T=T, M=M, result=res, witness=wit, cuts=cuts, seconds=round(time.time() - t0, 1))
    print(json.dumps(r), flush=True)
    with open('threshold_results.jsonl', 'a') as f: f.write(json.dumps(r) + '\n')
