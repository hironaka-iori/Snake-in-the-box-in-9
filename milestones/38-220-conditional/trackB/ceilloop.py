"""Witnessed ceiling of the shape automaton with per-shape combined floors.
U[s] = smallest validated local W12 = sum_7(24 alpha + share12) known for shape s (real snakes,
CP-SAT, CaDiCaL).  Any per-shape floor Y(s) <= U[s], so the min cycle mean of U over the shape
graph caps what the candidate can prove.  Loop: find a min-mean cycle of U, improve the witnesses
of its shapes (CP-SAT, hinted with the best selection), repeat.  usage: ceilloop.py rounds tl"""
import json, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from shapegraph import shapes, graph
import seeds as SD
from combined import exact, window_from_dirs
from sawit import check
WFILE = os.path.join(HERE, 'data', 'witness_W24.jsonl')

def load():
    U = {}
    if os.path.exists(WFILE):
        for l in open(WFILE):
            r = json.loads(l); s = tuple(r['dirs'])
            if s not in U or r['value'] < U[s]['value']: U[s] = r
    return U

def add(r):
    with open(WFILE, 'a') as f: f.write(json.dumps(r) + '\n')

def init_real(S):
    U = load(); want = set(S)
    best = {}
    for p, Sset in SD.bank_paths():
        for c, sel in SD.occurrences(p, Sset):
            if c not in want: continue
            w = window_from_dirs(list(c))
            sel = [v for v in sel if min(bin(v ^ x).count('1') for x in w) <= 4]
            A, SH = exact(w, sel, 12); v = 24 * sum(A) + sum(SH)
            if c not in best or v < best[c][0]: best[c] = (v, sel)
    for c, (v, sel) in best.items():
        if c not in U or v < U[c]['value']:
            r = dict(dirs=list(c), value=v, src='bank', sel=sel); add(r); U[c] = r
    for fn in ('sweep_comb24.jsonl', 'tradeoff.jsonl', 'levels.jsonl'):
        p = os.path.join(HERE, 'data', fn)
        if not os.path.exists(p): continue
        for l in open(p):
            r = json.loads(l)
            if r.get('wA', 24) != 24 and 'W' not in r: continue
            v = r.get('value', r.get('W')); sel = r.get('sel')
            if v is None or not sel: continue
            if fn != 'levels.jsonl' and not r.get('valid_cnf'): continue
            c = tuple(r['dirs'])
            if c not in U or v < U[c]['value']:
                rr = dict(dirs=list(c), value=v, src=fn, sel=sel); add(rr); U[c] = rr
    return U

def min_cycle(E, U, S):
    """Lawler: binary search on mu with Bellman-Ford negative-cycle detection (weights on states)."""
    V = [s for s in S if s in U]
    def neg_cycle(mu):
        dist = {s: 0.0 for s in V}; par = {s: None for s in V}; last = None
        for it in range(len(V)):
            last = None
            for s in V:
                for t in E[s]:
                    if t in dist and dist[s] + U[t]['value'] - mu < dist[t] - 1e-9:
                        dist[t] = dist[s] + U[t]['value'] - mu; par[t] = s; last = t
            if last is None: return None
        x = last
        for _ in range(len(V)): x = par[x]
        cyc = [x]; y = par[x]
        while y != x: cyc.append(y); y = par[y]
        return cyc[::-1]
    lo, hi = 0.0, 5000.0; cyc = None
    for _ in range(40):
        mid = (lo + hi) / 2; c = neg_cycle(mid)
        if c: hi = mid; cyc = c
        else: lo = mid
    return cyc, (sum(U[s]['value'] for s in cyc) / len(cyc) if cyc else None)

def improve(s, U, tl):
    from cpmin import minimize
    hint = set(U[s]['sel']) if s in U else None
    r = minimize(list(s), tl=tl, wA=24, workers=4, hint=hint)
    if 'sel' in r and check(window_from_dirs(list(s)), r['sel']):
        if s not in U or r['value'] < U[s]['value']:
            rr = dict(dirs=list(s), value=r['value'], src='cpsat', sel=r['sel'], lb=r['lb']); add(rr); U[s] = rr
            return r['value']
    return None

if __name__ == '__main__':
    rounds, tl = int(sys.argv[1]), float(sys.argv[2])
    S = shapes(); E = graph(S); U = init_real(S)
    missing = [s for s in S if s not in U]
    print('witnessed shapes', len(U), 'missing', len(missing), flush=True)
    if os.environ.get('MISSING'):
        for s in missing:
            print('missing', s, improve(s, U, tl), flush=True)
    tried = {}
    for rd in range(rounds):
        cyc, mu = min_cycle(E, U, S)
        print(f'round {rd}: min cycle mean {mu:.1f} len {len(cyc)}', [''.join(map(str, c)) for c in cyc],
              [U[c]['value'] for c in cyc], flush=True)
        if mu < 1133:
            print('BELOW 1133: candidate dead for 220'); break
        cand = sorted(cyc, key=lambda c: (tried.get(c, 0), -U[c]['value']))[0]
        tried[cand] = tried.get(cand, 0) + 1
        print('  improve', cand, U[cand]['value'], '->', improve(cand, U, tl), flush=True)
