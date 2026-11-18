"""CP-SAT minimisation of the combined window weight W = sum_centres (wA alpha + share_M)
in the radius-R local model of wincert.Encoding (counts free unless given).  Same constraints:
window selected, degree <= 2 inside the ball, interior selected vertices degree >= 1 and at most
`ends` of them degree 1, no selected square, no 6-cycle in a 3-cube, lazy cuts for cycles.
Returns (best value, proven lower bound, selection).  Solver-only (truth check), not a certificate."""
import sys, os, json, itertools, time
from ortools.sat.python import cp_model
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from combined import exact, window_from_dirs
import wincert

def model(w, R=4, M=12, wA=24, ends=2, cap=None, alpha=None, share_ci=None, asum=None, m=None, raw=False):
    ball = [v for v in range(512) if min(bin(v ^ x).count('1') for x in w) <= R]
    B = set(ball)
    own = m is None
    if own: m = cp_model.CpModel()
    X = {v: m.NewBoolVar('') for v in ball}
    for v in w: m.Add(X[v] == 1)
    endv = []
    for v in ball:
        ns = [X[v ^ 1 << k] for k in range(9) if v ^ 1 << k in B]
        # deg <= 2 if selected
        m.Add(sum(ns) <= 2).OnlyEnforceIf(X[v])
        if len(ns) == 9:
            m.Add(sum(ns) >= 1).OnlyEnforceIf(X[v])
            e = m.NewBoolVar(''); endv.append(e)
            # e <-> X[v] and deg == 1  (only need: X[v] and deg<=1 -> e)
            m.Add(sum(ns) >= 2).OnlyEnforceIf([X[v], e.Not()])
    m.Add(sum(endv) <= ends)
    for v in ball:
        for a, b in itertools.combinations(range(9), 2):
            if v >> a & 1 or v >> b & 1: continue
            sq = [v, v | 1 << a, v | 1 << b, v | 1 << a | 1 << b]
            if all(u in B for u in sq): m.AddBoolOr([X[u].Not() for u in sq])
        for t in itertools.combinations(range(9), 3):
            if any(v >> k & 1 for k in t): continue
            cube = [v ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
            if all(u in B for u in cube):
                for r in range(4):
                    m.AddBoolOr([X[cube[s]].Not() for s in range(8) if s not in (r, 7 - r)])
    obj = []; alist = []
    cis = range(1, len(w) - 1) if share_ci is None else share_ci
    for ci in range(1, len(w) - 1):
        c = w[ci]
        used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
        corners = [X[c ^ 1 << a ^ 1 << b] for a, b in itertools.combinations(range(9), 2)
                   if a not in used and b not in used]
        al = 21 - sum(corners)
        if alpha is not None and alpha[ci - 1] is not None:
            lo, hi = alpha[ci - 1]
            m.Add(al >= lo); m.Add(al <= hi)
        alist.append(al)
        if wA: obj.append(wA * al)
        if ci not in cis: continue
        for kk in range(9):
            if kk in used: continue
            q = c ^ 1 << kk
            Es = []
            for a, b in itertools.combinations(range(9), 2):
                if kk in (a, b): continue
                sq = [q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b]
                e = m.NewBoolVar('')
                for u in sq: m.AddImplication(e, X[u].Not())
                m.AddBoolOr([X[u] for u in sq] + [e])
                Es.append(e)
            d = sum(X[q ^ 1 << t] for t in range(9))
            s = m.NewIntVar(0, 28 * M, '')
            for dd in range(1, 10):
                D = m.NewBoolVar('')
                m.Add(d == dd).OnlyEnforceIf(D)
                m.Add(d != dd).OnlyEnforceIf(D.Not())
                m.Add(dd * s >= M * sum(Es) - dd + 1).OnlyEnforceIf(D)
            obj.append(s)
    if asum is not None: m.Add(sum(alist) <= asum)
    W = sum(obj)
    if raw: return X, ball, W, alist
    if cap is not None: m.Add(W <= cap)
    m.Minimize(W)
    return m, X, ball

def minimize(dirs, R=4, M=12, wA=24, tl=300, workers=4, alpha=None, hint=None, log=False, asum=None):
    w = window_from_dirs(list(dirs))
    m, X, ball = model(w, R, M, wA, alpha=alpha, asum=asum)
    t0 = time.time(); cuts = 0
    while True:
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = max(60, tl - (time.time() - t0))
        s.parameters.num_workers = workers
        if hint:
            for v in ball: m.AddHint(X[v], 1 if v in hint else 0)
        st = s.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return dict(dirs=list(dirs), asum=asum, wA=wA, status=s.StatusName(st), lb=s.BestObjectiveBound(), seconds=round(time.time()-t0,1))
        sel = [v for v in ball if s.Value(X[v])]
        cyc = wincert.cycles_of(sel)
        if not cyc or time.time() - t0 > tl + float(os.environ.get('EXTRA', 600)):
            A, SH = exact(w, sel, M)
            return dict(dirs=list(dirs), asum=asum, wA=wA, status=s.StatusName(st) if not cyc else 'CYCLE', value=wA * sum(A) + sum(SH),
                        lb=s.BestObjectiveBound(), alpha=A, share=SH, cuts=cuts, seconds=round(time.time()-t0,1), sel=sel)
        for c in cyc:
            m.AddBoolOr([X[u].Not() for u in c]); cuts += 1
        m.ClearHints()
        for v in ball: m.AddHint(X[v], 1 if v in sel else 0)
        hint = None
        tl_step = 60

if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    wA = int(sys.argv[3]) if len(sys.argv) > 3 else 24
    asum = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != '-' else None
    out = sys.argv[5] if len(sys.argv) > 5 else None
    r = minimize(dirs, tl=tl, wA=wA, workers=int(os.environ.get('W', 4)), asum=asum)
    if 'sel' in r:
        from sawit import check
        r['valid_cnf'] = bool(check(window_from_dirs(list(dirs)), r['sel']))
    if out:
        with open(out, 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps({k: v for k, v in r.items() if k != 'sel'}), flush=True)
