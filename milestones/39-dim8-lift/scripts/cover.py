"""Independent check of the orbit cover behind the cubes (SAT side; the Lean version would replay the
same CNFs).  Claim C5: every set of Q5 vertices with >= 15 vertices, induced degree <= 2 and a level
function (every selected vertex with two selected neighbours has a selected neighbour of smaller level,
levels <= 64) is one of the raw sets listed by enumk_raw.  Claim C6(r), for each Q5 representative r:
every such set of Q6 whose x5 = 0 half is exactly r and whose other half B has
29 - |r| <= |B| <= |r| is one of the unions listed by enum6_raw for r.  Both are checked as CNF UNSAT
(blocking clauses for the listed sets).  Also checks that each listed set is mapped by its stored
group element (coordinate permutation index p, translation t) onto its listed canonical form, and
that the canonical forms are exactly the representative files.
usage: python3 cover.py raw5.txt raw6.txt outdir"""
import sys, os, json, itertools, subprocess, time
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
raw5, raw6, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
D = 64

def base(k, pool, s):
    V = 1 << k; cl = []
    for u in range(V):
        nb = [s[u ^ (1 << i)] for i in range(k)]
        for a, b, c in combinations(nb, 3):
            cl.append([-s[u], -a, -b, -c])
    o = {(u, j): pool.id(('o', u, j)) for u in range(V) for j in range(1, D + 1)}
    for u in range(V):
        for j in range(1, D):
            cl.append([-o[u, j + 1], o[u, j]])
        al = {}
        for j in range(1, D + 1):
            for i in range(k):
                y = u ^ (1 << i); a = pool.id(('a', u, i, j)); al[i, j] = a
                cl += [[-a, s[y]], [-a, -o[y, j]]]
        for i1, i2 in combinations(range(k), 2):
            pre = [-s[u], -s[u ^ (1 << i1)], -s[u ^ (1 << i2)]]
            cl.append(pre + [o[u, 1]])
            for j in range(1, D + 1):
                cl.append(pre + ([o[u, j + 1]] if j < D else []) + [al[i, j] for i in range(k)])
    return cl

def card(lits, lo=None, hi=None, pool=None):
    cl = []
    if lo is not None:
        c = CardEnc.atleast(lits, bound=lo, top_id=pool.top, encoding=EncType.seqcounter); cl += c.clauses; pool.top = max(pool.top, c.nv)
    if hi is not None:
        c = CardEnc.atmost(lits, bound=hi, top_id=pool.top, encoding=EncType.seqcounter); cl += c.clauses; pool.top = max(pool.top, c.nv)
    return cl

def solve(cl, nv, name):
    f = os.path.join(out, name + '.cnf')
    with open(f, 'w') as g:
        g.write('p cnf %d %d\n' % (nv, len(cl)))
        for c in cl: g.write(' '.join(map(str, c)) + ' 0\n')
    t = time.time(); r = subprocess.run(['cadical', '-q', f], capture_output=True, text=True); os.remove(f)
    st = [x for x in r.stdout.split('\n') if x.startswith('s ')]
    return (st[0][2:] if st else 'ERR'), round(time.time() - t, 2), len(cl)

def perms(k): return list(itertools.permutations(range(k)))
def apply(m, p, t, k):
    r = 0
    for u in range(1 << k):
        if m >> u & 1:
            w = sum(1 << p[i] for i in range(k) if u >> i & 1)
            r |= 1 << (w ^ t)
    return r

res = {}
# ---- C5
P5 = perms(5)
R5 = [l.split() for l in open(raw5) if l.startswith('R ')]
reps5 = {int(l.split()[2], 16) for l in open(os.path.join(os.path.dirname(__file__), '..', 'data', 'q5_15.txt'))}
ok = all(apply(int(m, 16), P5[int(p)], int(t), 5) == int(c, 16) for _, m, c, p, t in R5)
res['C5_group_elements_ok'] = ok and {int(c, 16) for _, _, c, _, _ in R5} == reps5
pool = IDPool(); s = [pool.id(('s', u)) for u in range(32)]
cl = base(5, pool, s) + card(s, lo=15, pool=pool)
for _, m, _, _, _ in R5:
    m = int(m, 16); cl.append([(-s[u] if m >> u & 1 else s[u]) for u in range(32)])
res['C5'] = solve(cl, pool.top, 'C5')
print('C5', res['C5'], res['C5_group_elements_ok'], flush=True)
# ---- C6(r)
P6 = perms(6)
reps6 = {int(l.split()[2], 16) for l in open(os.path.join(os.path.dirname(__file__), '..', 'data', 'q6_29.txt'))}
by = {}
allok = True; canon = set()
for _, m, c, p, t in (l.split() for l in open(raw6) if l.startswith('R ')):
    m = int(m, 16); c = int(c, 16)
    if apply(m, P6[int(p)], int(t), 6) != c: allok = False
    canon.add(c); by.setdefault(m & 0xffffffff, []).append(m >> 32)
res['C6_group_elements_ok'] = allok and canon == reps6
print('C6 group elements', res['C6_group_elements_ok'], len(by), flush=True)
res['C6'] = {}
for r in sorted(reps5):
    a = bin(r).count('1')
    pool = IDPool(); s = [pool.id(('s', u)) for u in range(64)]
    cl = base(6, pool, s)
    cl += [[s[u]] if r >> u & 1 else [-s[u]] for u in range(32)]
    cl += card([s[32 + u] for u in range(32)], lo=29 - a, hi=a, pool=pool)
    for B in by.get(r, []):
        cl.append([(-s[32 + u] if B >> u & 1 else s[32 + u]) for u in range(32)])
    res['C6']['%08x' % r] = solve(cl, pool.top, 'C6_%08x' % r) + (len(by.get(r, [])),)
    print('C6', '%08x' % r, res['C6']['%08x' % r], flush=True)
res['all_unsat'] = res['C5'][0] == 'UNSATISFIABLE' and all(v[0] == 'UNSATISFIABLE' for v in res['C6'].values())
json.dump(res, open(os.path.join(out, 'cover_check.json'), 'w'), indent=1)
print('ALL UNSAT:', res['all_unsat'])
