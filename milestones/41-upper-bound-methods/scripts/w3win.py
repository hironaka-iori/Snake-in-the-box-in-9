"""Free window floors of the k-subcube census weight w_k (milestone 22 section 5).

w_k(x) = sum over the C(9,k) k-subcubes Q containing x of 1/|Q cap S|;  sum_{x in S} w_k(x) <= N_k.
For a window shape (direction list, t centres) we minimise sum_{centres} L*w_k(centre) (L = lcm scaling)
subject to the radius-r window CNF of milestones 10/28 (wincert.Encoding with free counts: degree <= 2,
endpoint budget, no 4- and 6-cycles, lazy cycle cuts).  This is the quantity that a w_k window automaton
starts from (the analogue of the free alpha floor).  CP-SAT, solver evidence only.
usage: python3 w3win.py k radius seconds workers t [t ...]      (all shapes with t centres)"""
import os, sys, json, time, itertools
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__)); MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
from wincert import Encoding, window_from_dirs, cycles_of
from ortools.sat.python import cp_model
from fractions import Fraction


def shapes(t):
    """Canonical direction lists of length t+1 (first-occurrence order) giving induced paths."""
    out = []
    def rec(ds, mx):
        if len(ds) == t + 1:
            w = window_from_dirs(ds)
            ok = len(set(w)) == len(w) and all((w[i] ^ w[j]).bit_count() >= 2 for i in range(len(w)) for j in range(i + 2, len(w)))
            if ok: out.append(list(ds))
            return
        for d in range(min(mx + 2, 9)):
            if ds and d == ds[-1]: continue
            rec(ds + [d], max(mx, d))
    rec([], -1)
    return out


def subcubes_at(x, k):
    for D in itertools.combinations(range(9), k):
        base = x & ~sum(1 << i for i in D)
        vs = [base]
        for i in D: vs = vs + [v | 1 << i for v in vs]
        yield vs


def floor_of(ds, k, radius, sec, wk):
    w = window_from_dirs(ds)
    enc = Encoding(w, [None] * (len(ds) - 1), radius)
    m = cp_model.CpModel()
    x = [None] + [m.NewBoolVar("") for _ in range(enc.nv)]
    lit = lambda l: x[l] if l > 0 else x[-l].Not()
    for c in enc.clauses: m.AddBoolOr([lit(l) for l in c])
    L = 60 if k == 3 else (5040 if k > 3 else 12)
    obj = []
    maxsz = {2: 3, 3: 5, 4: 9, 5: 17}[k]
    for c in w[1:-1]:
        for Q in subcubes_at(c, k):
            assert all(v in enc.B for v in Q)
            cnt = m.NewIntVar(1, maxsz, "")
            m.Add(cnt == sum(x[enc.var[v]] for v in Q))
            val = m.NewIntVar(L // maxsz, L, "")
            m.AddElement(cnt, [0] + [L // j for j in range(1, maxsz + 1)], val)
            obj.append(val)
    m.Minimize(sum(obj))
    t0 = time.time(); cuts = 0
    while True:
        s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = max(1, sec - (time.time() - t0)); s.parameters.num_workers = wk
        st = s.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return dict(dirs=ds, status=s.StatusName(st))
        sel = [v for v in enc.ball if s.Value(x[enc.var[v]])]
        cyc = cycles_of(sel)
        if not cyc:
            t = len(ds) - 1
            return dict(dirs=ds, k=k, radius=radius, status=s.StatusName(st), best=s.ObjectiveValue() / L / t,
                        bound=s.BestObjectiveBound() / L / t, cuts=cuts, seconds=round(time.time() - t0, 1))
        for cy in cyc:
            m.AddBoolOr([x[enc.var[v]].Not() for v in cy]); cuts += 1
        if time.time() - t0 > sec:
            return dict(dirs=ds, status='TIMEOUT', cuts=cuts)


if __name__ == '__main__':
    k, radius, sec, wk = map(int, sys.argv[1:5])
    for t in map(int, sys.argv[5:]):
        for ds in shapes(t):
            print(json.dumps(floor_of(ds, k, radius, sec, wk)), flush=True)
