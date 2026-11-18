"""Global-consistency ceiling (track B).  Fix an induced cycle P of Q9 (length p) and choose ONE
selection S of Q9 containing P such that every 7-centre window along P (9 consecutive vertices) is
a valid radius-R local model at once: degree <= 2 (globally), no selected square, no 3-cube
6-cycle, interior vertices of each ball have degree >= 1 and at most 2 of them degree 1, and no
cycle of S other than P lies inside a window ball (lazy cuts).  Minimise
mean over x in P of (24 alpha(x) + share12(x)).  Since the windows share one S, their counts are
consistent, so P is a cycle of every (shape, count) automaton and of every window of length up to
the largest one whose ball does not contain P: no such method can prove a larger per-vertex mean.
usage: globalcycle.py P.json tl [R]"""
import sys, os, json, itertools, time, random
from ortools.sat.python import cp_model
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)

def ball_of(vs, R):
    return [v for v in range(512) if min(bin(v ^ x).count('1') for x in vs) <= R]

def components(S):
    S = set(S); seen = set(); out = []
    for v in S:
        if v in seen: continue
        st = [v]; seen.add(v); comp = []
        while st:
            x = st.pop(); comp.append(x)
            for k in range(9):
                u = x ^ 1 << k
                if u in S and u not in seen: seen.add(u); st.append(u)
        out.append(comp)
    return out

def is_cycle(comp, S):
    return all(sum(1 for k in range(9) if x ^ 1 << k in S) == 2 for x in comp) and len(comp) >= 4

def measure(P, S, M=12):
    S = set(S); p = len(P); A = []; SH = []
    for i, x in enumerate(P):
        used = {(x ^ P[i - 1]).bit_length() - 1, (x ^ P[(i + 1) % p]).bit_length() - 1}
        A.append(sum(1 for a, b in itertools.combinations(range(9), 2)
                     if a not in used and b not in used and (x ^ 1 << a ^ 1 << b) not in S))
        sh = 0
        for kk in range(9):
            if kk in used: continue
            q = x ^ 1 << kk
            e0 = sum(1 for a, b in itertools.combinations(range(9), 2)
                     if not ({q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b} & S))
            d = sum(1 for t in range(9) if q ^ 1 << t in S)
            sh += (M * e0) // d
        SH.append(sh)
    return A, SH

def validate(P, S, R=4):
    """Every window along P is a model of the radius-R wincert CNF (counts free)."""
    sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
    from sawit import check
    p = len(P); S = set(S); bad = []
    for j in range(p):
        w = [P[(j + i) % p] for i in range(9)]
        B = set(ball_of(w, R))
        if not check(w, [v for v in S if v in B], R): bad.append(j)
    return bad

def solve(P, tl=600, R=4, M=12, workers=4, hint=None):
    p = len(P); Pset = set(P)
    m = cp_model.CpModel()
    X = {v: m.NewBoolVar('') for v in range(512)}
    for v in P: m.Add(X[v] == 1)
    nb = lambda v: [X[v ^ 1 << k] for k in range(9)]
    for v in range(512):
        m.Add(sum(nb(v)) <= 2).OnlyEnforceIf(X[v])
        for a, b in itertools.combinations(range(9), 2):
            if v >> a & 1 or v >> b & 1: continue
            m.AddBoolOr([X[u].Not() for u in (v, v | 1 << a, v | 1 << b, v | 1 << a | 1 << b)])
        for t in itertools.combinations(range(9), 3):
            if any(v >> k & 1 for k in t): continue
            cube = [v ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
            for r in range(4):
                m.AddBoolOr([X[cube[s]].Not() for s in range(8) if s not in (r, 7 - r)])
    # degree-1 and isolated indicators (global degree)
    one = {}
    for v in range(512):
        e = m.NewBoolVar(''); one[v] = e
        m.Add(sum(nb(v)) >= 2).OnlyEnforceIf([X[v], e.Not()])
    balls = []
    for j in range(p):
        w = [P[(j + i) % p] for i in range(9)]
        B = ball_of(w, R); Bs = set(B)
        inter = [v for v in B if all(v ^ 1 << k in Bs for k in range(9))]
        for v in inter: m.Add(sum(nb(v)) >= 1).OnlyEnforceIf(X[v])
        m.Add(sum(one[v] for v in inter) <= 2)
        balls.append(Bs)
    obj = []
    for i, x in enumerate(P):
        used = {(x ^ P[i - 1]).bit_length() - 1, (x ^ P[(i + 1) % p]).bit_length() - 1}
        corners = [X[x ^ 1 << a ^ 1 << b] for a, b in itertools.combinations(range(9), 2)
                   if a not in used and b not in used]
        obj.append(24 * (21 - sum(corners)))
        for kk in range(9):
            if kk in used: continue
            q = x ^ 1 << kk
            Es = []
            for a, b in itertools.combinations(range(9), 2):
                if kk in (a, b): continue
                sq = [q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b]
                e = m.NewBoolVar('')
                for u in sq: m.AddImplication(e, X[u].Not())
                m.AddBoolOr([X[u] for u in sq] + [e]); Es.append(e)
            d = sum(X[q ^ 1 << t] for t in range(9))
            s = m.NewIntVar(0, 28 * M, '')
            for dd in range(1, 10):
                D = m.NewBoolVar('')
                m.Add(d == dd).OnlyEnforceIf(D); m.Add(d != dd).OnlyEnforceIf(D.Not())
                m.Add(dd * s >= M * sum(Es) - dd + 1).OnlyEnforceIf(D)
            obj.append(s)
    m.Minimize(sum(obj))
    if hint:
        for v in range(512): m.AddHint(X[v], 1 if v in hint else 0)
    t0 = time.time(); cuts = 0; best = None
    while True:
        so = cp_model.CpSolver(); so.parameters.num_workers = workers
        so.parameters.max_time_in_seconds = max(60, tl - (time.time() - t0))
        st = so.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return dict(status=so.StatusName(st))
        S = [v for v in range(512) if so.Value(X[v])]
        Ss = set(S); bad = 0
        for comp in components(S):
            if set(comp) == Pset or not is_cycle(comp, Ss): continue
            if any(set(comp) <= Bs for Bs in balls):
                m.AddBoolOr([X[u].Not() for u in comp]); cuts += 1; bad += 1
        if not bad or time.time() - t0 > tl + 900:
            A, SH = measure(P, S, M)
            return dict(status=so.StatusName(st) if not bad else 'CYCLE', p=p, mean=(24 * sum(A) + sum(SH)) / p,
                        lb=so.BestObjectiveBound() / p, alpha_mean=sum(A) / p, share_mean=sum(SH) / p,
                        cuts=cuts, seconds=round(time.time() - t0), S=S, P=P)
        m.ClearHints()
        for v in range(512): m.AddHint(X[v], 1 if v in Ss else 0)

def random_cycle(L, seed=1, tries=200000):
    rnd = random.Random(seed)
    for _ in range(tries):
        path = [0]; S = {0}
        ok = True
        while len(path) < L:
            x = path[-1]
            cand = []
            for k in range(9):
                u = x ^ 1 << k
                if u in S: continue
                if sum(1 for t in range(9) if u ^ 1 << t in S) != 1: continue
                cand.append(u)
            if not cand: ok = False; break
            u = rnd.choice(cand); path.append(u); S.add(u)
        if not ok: continue
        # close: last must be adjacent to first? try to finish by requiring path[-1] ~ path[0]
        if bin(path[-1] ^ path[0]).count('1') == 1:
            # induced cycle check
            p = len(path); good = True
            for i in range(p):
                for j in range(i + 2, p):
                    if (i, j) == (0, p - 1): continue
                    if bin(path[i] ^ path[j]).count('1') == 1: good = False; break
                if not good: break
            if good: return path
    return None

if __name__ == '__main__':
    P = json.load(open(sys.argv[1])); tl = float(sys.argv[2]); R = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    r = solve(P, tl, R)
    if 'S' in r:
        r['bad_windows'] = validate(P, r['S'], R)
    with open(os.path.join(HERE, 'data', 'globalcycle.jsonl'), 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps({k: v for k, v in r.items() if k not in ('S', 'P')}), flush=True)
