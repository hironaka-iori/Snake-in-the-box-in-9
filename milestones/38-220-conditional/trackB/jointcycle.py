"""Witnessed ceiling for count-dependent window methods (track B).
Given a cyclic direction sequence D (period p; window j uses D[j..j+7], 7 centres at walk
positions j+1..j+7), find ONE periodic lumped count sequence s_0..s_{p-1} (s in 1..8, 8 = '>= 8')
and, for every window, its own radius-4 local model (wincert.Encoding constraints, lazy cycle cuts)
whose centre counts realise the lumped counts, minimising the total combined weight
sum_j W_j, W_j = sum_7 (24 alpha + share12).  If the optimum mean W_j is below the 220 threshold,
every method that sees only (shape, lumped counts) of 7-centre radius-4 windows -- any automaton,
any count-dependent share floors -- has this periodic walk with mean below threshold: a ceiling.
usage: jointcycle.py "D as json list" tl [out]"""
import sys, os, json, time
from ortools.sat.python import cp_model
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from cpmin import model, window_from_dirs, exact
from sawit import check
import wincert

def canon(ds):
    mp = {}; return [mp.setdefault(d, len(mp)) for d in ds]

def solve(D, tl=600, cap8=8, hints=None):
    """D: list of p canonical 8-direction shapes forming a cycle of the shape graph."""
    p = len(D)
    m = cp_model.CpModel()
    s = [m.NewIntVar(1, cap8, f's{t}') for t in range(p)]
    big = [m.NewBoolVar('') for t in range(p)]
    for t in range(p):
        m.Add(s[t] == cap8).OnlyEnforceIf(big[t]); m.Add(s[t] <= cap8 - 1).OnlyEnforceIf(big[t].Not())
    wins = []
    for j in range(p):
        w = window_from_dirs(list(D[j]))
        X, ball, W, al = model(w, m=m, raw=True)
        for i in range(7):
            t = (j + 1 + i) % p
            m.Add(al[i] == s[t]).OnlyEnforceIf(big[t].Not())
            m.Add(al[i] >= cap8).OnlyEnforceIf(big[t])
        wins.append((w, X, ball, W))
    m.Minimize(sum(W for _, _, _, W in wins))
    t0 = time.time(); cuts = 0
    while True:
        so = cp_model.CpSolver(); so.parameters.num_workers = 4
        so.parameters.max_time_in_seconds = max(60, tl - (time.time() - t0))
        st = so.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return dict(D=D, status=so.StatusName(st), lb=so.BestObjectiveBound())
        sels = [[v for v in ball if so.Value(X[v])] for w, X, ball, W in wins]
        bad = 0
        for (w, X, ball, W), sel in zip(wins, sels):
            for c in wincert.cycles_of(sel):
                m.AddBoolOr([X[u].Not() for u in c]); cuts += 1; bad += 1
        m.ClearHints()
        for (w, X, ball, W), sel in zip(wins, sels):
            ss = set(sel)
            for v in ball: m.AddHint(X[v], 1 if v in ss else 0)
        if hints is not None and not bad:
            pass
        if not bad or time.time() - t0 > tl + 900:
            Ws = []; valid = []
            for (w, X, ball, W), sel in zip(wins, sels):
                A, SH = exact(w, sel, 12); Ws.append(24 * sum(A) + sum(SH)); valid.append(bool(check(w, sel)))
            return dict(D=D, status=so.StatusName(st) if not bad else 'CYCLE', counts=[so.Value(x) for x in s],
                        W=Ws, mean=sum(Ws) / p, lb=so.BestObjectiveBound() / p, valid=valid, cuts=cuts,
                        seconds=round(time.time() - t0), sels=sels)

if __name__ == '__main__':
    D = json.loads(sys.argv[1]); tl = float(sys.argv[2])
    r = solve(D, tl)
    out = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, 'data', 'jointcycle.jsonl')
    with open(out, 'a') as f: f.write(json.dumps(r) + '\n')
    print(json.dumps({k: v for k, v in r.items() if k != 'sels'}))
