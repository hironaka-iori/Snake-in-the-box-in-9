"""SAT search for induced 2-regular vertex sets with every cycle of length >= g.

mode q9   : S subset of Q_n (n=9 default), |S| >= target.
mode fib7 : A,B disjoint in Q7, |A|+|B| >= target (S = alternating fibres over Q2, |S| = 2(|A|+|B|)).
mode fib8 : A,B in Q8 general with vertical edges = Q9 itself, not used.

Cycle-length constraint is complete via an orientation + label encoding:
each selected vertex has exactly one out- and one in-edge; label l(v) in 0..M (M=2g-2);
non-root v (l(v)>=1) with predecessor u has l(v)=l(u)+1; a root (l=0) has predecessor with l>=g-1.
usage: python sat2reg.py mode g target timelimit out.json [solver] [card-enc] [sym]
"""
import sys, json, time, itertools, threading
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

mode, g, target, tl, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
sname = sys.argv[6] if len(sys.argv) > 6 else 'cadical195'
enc = getattr(EncType, sys.argv[7] if len(sys.argv) > 7 else 'seqcounter')
sym = sys.argv[8] if len(sys.argv) > 8 else ''

pool = IDPool(); cls = []
def V(*k): return pool.id(k)

if mode == 'q9':
    n = 9; verts = [(0, v) for v in range(1 << n)]
    def nbrs(c, v): return [(c, v ^ 1 << k) for k in range(n)]
    copies = [0]
elif mode == 'fib7':
    n = 7; verts = [(c, v) for c in (0, 1) for v in range(1 << n)]
    def nbrs(c, v): return [(c, v ^ 1 << k) for k in range(n)]
    copies = [0, 1]
    for v in range(1 << n): cls.append([-V('x', 0, v), -V('x', 1, v)])
M = 2 * g - 2
X = lambda w: V('x', *w)
D = lambda a, b: V('d', a, b)
Y = lambda w, k: V('y', w, k)
for w in verts:
    N = nbrs(*w)
    outs = [D(w, z) for z in N]; ins = [D(z, w) for z in N]
    # selected -> exactly one out, exactly one in
    cls.append([-X(w)] + outs); cls.append([-X(w)] + ins)
    for a, b in itertools.combinations(outs, 2): cls.append([-a, -b])
    for a, b in itertools.combinations(ins, 2): cls.append([-a, -b])
    for z in N:
        if z < w: continue
        cls.append([-D(w, z), -D(z, w)])
        cls.append([-X(w), -X(z), D(w, z), D(z, w)])
    for z in N:
        cls.append([-D(w, z), X(w)]); cls.append([-D(w, z), X(z)])
    for k in range(1, M):
        cls.append([-Y(w, k + 1), Y(w, k)])
# label propagation
for w in verts:
    for z in nbrs(*w):
        d = D(w, z)
        # z non-root: l(z)=l(w)+1
        cls.append([-d, -Y(z, 1), -Y(w, M)])
        for k in range(1, M):
            cls.append([-d, -Y(z, 1), -Y(w, k), Y(z, k + 1)])
            cls.append([-d, -Y(z, 1), Y(w, k), -Y(z, k + 1)])
        # z root: l(w) >= g-1
        cls.append([-d, Y(z, 1), Y(w, g - 1)])
# symmetry breaking / structure
cls.append([X(verts[0])])
if sym.startswith('t'):  # invariance under translation by t (q9 only): S = S xor t
    t = int(sym[1:])
    for v in range(512):
        if v < v ^ t: cls.append([-X((0, v)), X((0, v ^ t))]); cls.append([X((0, v)), -X((0, v ^ t))])
lits = [X(w) for w in verts]
card = CardEnc.atleast(lits, bound=target, vpool=pool, encoding=enc)
cls += card.clauses
print(f"mode={mode} g={g} target={target} vars={pool.top} clauses={len(cls)} enc={enc} sym={sym}", flush=True)
s = Solver(name=sname, bootstrap_with=cls)
timer = threading.Timer(tl, lambda: s.interrupt()); timer.start()
t0 = time.time()
r = s.solve_limited(expect_interrupt=True)
timer.cancel()
print("result", r, f"time={time.time()-t0:.1f}", flush=True)
if r:
    m = set(l for l in s.get_model() if l > 0)
    sel = [w for w in verts if X(w) in m]
    res = {'mode': mode, 'g': g}
    if mode == 'q9':
        res['S'] = sorted(v for c, v in sel)
    else:
        A = sorted(v for c, v in sel if c == 0); B = sorted(v for c, v in sel if c == 1)
        S = sorted({u | (y << 7) for y in range(4) for u in (A if bin(y).count('1') % 2 == 0 else B)})
        res.update({'A': A, 'B': B, 'S': S})
    json.dump(res, open(out, 'w'))
    print("saved", out, "size", len(res['S']), flush=True)
