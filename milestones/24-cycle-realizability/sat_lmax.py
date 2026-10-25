"""SAT test 'the cyclic shape walk can be followed for n transitions from `phase`' (CaDiCaL
via pysat).  Used where the DFS of unroll.c does not finish: L_max = the largest SAT n.

Variables: y[t][k] (direction t is coordinate k), d[i][j][k] (parity of coordinate k on the
segment of directions i..j-1).  Constraints: the first 7 directions are the start shape
(wlog), each later direction follows its rule (repeat x_{t-delta}, or differ from the last 6),
exactly one coordinate per direction, value precedence for the coordinates not in the start
window, and for every segment of >= 2 directions at least two odd coordinates (induced path).

  python sat_lmax.py NAME PHASE N [N2 ...]       (NAME from data/cycles.json)
"""
import sys, json, os, time, itertools
from pysat.solvers import Solver
from shapes import rules_of_cycle

HERE = os.path.dirname(os.path.abspath(__file__))


def encode(states, phase, n):
    p = len(states)
    st = [tuple(states[(phase + i) % p]) for i in range(p)]
    rules = rules_of_cycle(st)
    T = 7 + n
    cnt = [0]

    def new():
        cnt[0] += 1
        return cnt[0]
    y = [[new() for _ in range(9)] for _ in range(T)]
    cl = []
    w0 = st[0]
    for t in range(7):
        for k in range(9):
            cl.append([y[t][k]] if w0[t] == k else [-y[t][k]])
    for t in range(7, T):
        cl.append([y[t][k] for k in range(9)])
        for a, b in itertools.combinations(range(9), 2):
            cl.append([-y[t][a], -y[t][b]])
        r = rules[(t - 7) % p]
        if r > 0:
            for k in range(9):
                cl.append([-y[t][k], y[t - r][k]]); cl.append([y[t][k], -y[t - r][k]])
        else:
            for j in range(1, 7):
                for k in range(9):
                    cl.append([-y[t][k], -y[t - j][k]])
    # value precedence for coordinates not in the start window
    m = max(w0) + 1
    for k in range(m + 1, 9):
        for t in range(7, T):
            cl.append([-y[t][k]] + [y[s][k - 1] for s in range(7, t)])
    # parities and the induced-path condition
    for i in range(T):
        prev = [y[i][k] for k in range(9)]
        for j in range(i + 2, T + 1):
            cur = []
            for k in range(9):
                a, b, c = prev[k], y[j - 1][k], new()
                cl += [[-c, a, b], [-c, -a, -b], [c, -a, b], [c, a, -b]]
                cur.append(c)
            if j - i >= 2:
                cl.append(cur[:])
                for k in range(9):
                    cl.append([cur[kk] for kk in range(9) if kk != k])
            prev = cur
    return cl, y


def solve(states, phase, n, name='cadical153'):
    cl, y = encode(states, phase, n)
    with Solver(name=name, bootstrap_with=cl) as s:
        ok = s.solve()
        seq = None
        if ok:
            mdl = set(v for v in s.get_model() if v > 0)
            seq = [next(k for k in range(9) if y[t][k] in mdl) for t in range(len(y))]
        return ok, seq


if __name__ == '__main__':
    from shapes import check_sequence
    cyc = json.load(open(os.path.join(HERE, 'data', 'cycles.json')))
    name, ph = sys.argv[1], int(sys.argv[2])
    st = [tuple(s) for s in cyc[name]['states']]
    for n in map(int, sys.argv[3:]):
        t = time.time()
        ok, seq = solve(st, ph, n)
        if ok:
            check_sequence(seq, st, ph)
        print(json.dumps(dict(name=name, phase=ph, n=n, sat=ok, seconds=round(time.time() - t, 1), seq=seq)), flush=True)
