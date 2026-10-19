"""How many empty squares does the local window model force at the unselected neighbours of a centre?
Uses the radius-r CNF of milestones/10-window-aggregate/scripts/wincert.py (Encoding), solved with Glucose4
(not CaDiCaL), with the same lazy cycle-cut loop.  E(q,ij) <- square {q,q^i,q^j,q^ij} empty.
Reports min sum_q e0(q) over the 7 unselected neighbours q of the centre (unweighted incidences), and the
min of 2*sum_q e0(q)/(2*dmax) is not needed: we report raw incidences."""
import sys, itertools
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../10-window-aggregate/scripts'))
import wincert
from pysat.solvers import Glucose4

def solve(enc, extra):
    with Glucose4(bootstrap_with=enc.clauses + extra) as s:
        cuts = 0
        while True:
            if not s.solve(): return 'UNSAT', cuts
            m = s.get_model()
            sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = wincert.cycles_of(sel)
            if not cyc: return 'SAT', cuts
            for c in cyc:
                s.add_clause([-enc.var[w] for w in c]); cuts += 1
            if cuts > 3000: return 'UNKNOWN', cuts

def run(dirs, centre_idx, radius, alpha, Kmax=60):
    from pysat.card import ITotalizer
    win = wincert.window_from_dirs(dirs)
    al = [None] * (len(win) - 2)
    al[centre_idx - 1] = alpha
    enc = wincert.Encoding(win, al, radius)
    X = enc.var
    c = win[centre_idx]
    used = {(c ^ win[centre_idx - 1]).bit_length() - 1, (c ^ win[centre_idx + 1]).bit_length() - 1}
    Es = []
    for k in range(9):
        if k in used: continue
        q = c ^ 1 << k
        for i, j in itertools.combinations(range(9), 2):
            if k in (i, j): continue
            sq = [q, q ^ 1 << i, q ^ 1 << j, q ^ 1 << i ^ 1 << j]
            if not all(w in enc.B for w in sq): continue
            e = enc.fresh(); Es.append(e)
            enc.add([X[w] for w in sq] + [e], 'empty->E')
    tot = ITotalizer(lits=Es, ubound=Kmax + 1, top_id=enc.nv)
    cuts = 0
    with Glucose4(bootstrap_with=enc.clauses + tot.cnf.clauses) as s:
        for K in range(0, Kmax + 1):
            while True:
                if not s.solve(assumptions=[-tot.rhs[K]]): break
                m = s.get_model()
                sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
                cyc = wincert.cycles_of(sel)
                if not cyc: return K, len(Es), cuts
                for cc in cyc:
                    s.add_clause([-enc.var[w] for w in cc]); cuts += 1
    return f'>{Kmax}', len(Es), cuts

if __name__ == '__main__':
    radius = int(sys.argv[1]); cases = {'c1': ([0, 1], 1, '1 centre'), 'c3a': ([0, 1, 2, 0], 2, '3 centres 0120, middle'), 'c3b': ([0, 1, 2, 3], 2, '3 centres 0123, middle')}
    for key in sys.argv[2].split(','):
        dirs, ci, lab = cases[key]
        for alpha in [(1, 3)]:
            r = run(dirs, ci, radius, alpha)
            print(f'radius {radius} {lab:26s} alpha {alpha}: min empty-square incidences at the 7 free neighbours = {r[0]} (of {r[1]} modelled squares; cuts {r[2]})', flush=True)
