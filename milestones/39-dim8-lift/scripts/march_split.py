"""Cube-and-conquer split of one cube with march_cu (lookahead cubing), output in split.py's format.

usage: python3 march_split.py L k A.json outdir T0 jobs MARCH [march args...]
  e.g. python3 march_split.py 116 29 A.json out 0 3 /opt/CnC/march_cu/march_cu -d 4

1. base.cnf   the Lean-exported cubeCnfQ 13 L A k (as split.py with GEN=lean ENC=q; reused if present)
2. march_cu   base.cnf -o outdir/cubes.icnf [march args]; every line "a l1 ... lm 0" is a cube.
3. tree       the cubes are paths of march's binary decision tree. A branch march refuted during
              lookahead has no cube, so the trie is completed: at an internal node with only one
              child, the missing sibling path is added as an extra leaf (it is UNSAT, and cheap: march
              refuted it). The completed leaves cover every assignment of the branch variables (checked
              here), as Dim8Lift.Split.ST requires. A trie node whose children branch on two different
              variables is rejected (exit 2).
4. solve      with T0 > 0, every leaf is solved by CaDiCaL with time limit T0 (status UNSATISFIABLE,
              SATISFIABLE or UNKNOWN; a SAT leaf makes result NOT-UNSAT; T0 only sizes the leaves). With T0 = 0 the leaves are
              not solved here (status CUBE); make_cert.py solves each one when it certifies it.
nodes.jsonl gets one line per leaf {lits, status, sec, src: march|sibling}; the last stdout line is the
JSON summary (result UNSAT when no leaf is SAT), as split.py prints it.
"""
import sys, os, json, subprocess, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
L, k = int(sys.argv[1]), int(sys.argv[2]); Af = sys.argv[3]; out = sys.argv[4]; T0 = int(sys.argv[5]); jobs = int(sys.argv[6])
march = sys.argv[7]; margs = sys.argv[8:]
os.makedirs(out, exist_ok=True)
A = set(json.load(open(Af))); assert len(A) == k
base = os.path.join(out, 'base.cnf')
if not os.path.exists(base):
    lean = os.path.join(HERE, '..', 'lean'); mask = '%016x' % sum(1 << u for u in A)
    subprocess.run(['/opt/lean-4.35.0-linux/bin/lean', '--run', 'Export.lean', '13', str(L), mask, str(k), base + '.tmp', 'q'],
                   check=True, capture_output=True, cwd=lean, env=dict(os.environ, LEAN_PATH=os.path.join(lean, 'build')))
    os.rename(base + '.tmp', base)
hdr = open(base).readline().split(); NV, NC = int(hdr[2]), int(hdr[3])
t0 = time.time()

# 2. cubes
icnf = os.path.join(out, 'cubes.icnf')
if not os.path.exists(icnf):
    r = subprocess.run([march, base, '-o', icnf + '.tmp'] + margs, capture_output=True, text=True)
    open(os.path.join(out, 'march.log'), 'w').write(r.stdout + r.stderr)
    if 'UNSATISFIABLE' in r.stdout and not os.path.exists(icnf + '.tmp'):
        open(icnf + '.tmp', 'w').close()   # refuted outright: no cubes, the completed tree is the root alone
    assert os.path.exists(icnf + '.tmp'), 'march_cu wrote no cubes (rc %d): %s' % (r.returncode, (r.stdout + r.stderr)[-500:])
    os.rename(icnf + '.tmp', icnf)
cubes = []
for line in open(icnf):
    t = line.split()
    if not t or t[0] != 'a': continue
    assert t[-1] == '0', line
    c = tuple(int(x) for x in t[1:-1]); assert all(0 < abs(x) <= NV for x in c), line
    assert len({abs(x) for x in c}) == len(c), ('repeated variable in a cube', line)
    cubes.append(c)
march_wall = round(time.time() - t0)

# 3. trie of the cube paths, completed with the refuted siblings
cs = set(cubes); assert len(cs) == len(cubes), 'duplicate cubes'
pre = {}   # prefix -> set of next literals
for c in cs:
    for i in range(len(c)):
        pre.setdefault(c[:i], set()).add(c[i])
for c in cs:
    assert c not in pre, ('a cube is a prefix of another cube', c)
extra = []
for p, nxt in pre.items():
    vs = {abs(x) for x in nxt}
    if len(vs) != 1:
        print(json.dumps(dict(result='BAD-TREE', prefix=list(p), next=sorted(nxt)))); sys.exit(2)
    v = vs.pop()
    for s in (v, -v):
        if s not in nxt: extra.append(p + (s,))
leaves = [(c, 'march') for c in sorted(cs)] + [(c, 'sibling') for c in sorted(extra)]
if not cubes: leaves = [((), 'sibling')]   # march refuted the cube: the root is the only leaf
# coverage check: the leaves are exactly the leaves of a full binary tree (each internal node has 2 children)
P = set(pre)
LS = {c for c, _ in leaves}; assert len(LS) == len(leaves)
for p in P:
    v = abs(next(iter(pre[p])))
    assert all(p + (x,) in P or p + (x,) in LS for x in (v, -v)), p
assert all(c[:-1] in P for c, _ in leaves if c)

# 4. solve the leaves (optional)
body = open(base).read().split('\n', 1)[1]
def solve(c):
    if T0 <= 0: return 'CUBE', 0.0
    f = os.path.join(out, 'leaf_%d.cnf' % (abs(hash(c)) % 10**9))
    with open(f, 'w') as g:
        g.write('p cnf %d %d\n' % (NV, NC + len(c))); g.write(body)
        for x in c: g.write('%d 0\n' % x)
    s = time.time(); r = subprocess.run(['cadical', '-q', '-t', str(T0), f], capture_output=True, text=True); os.remove(f)
    st = [x for x in r.stdout.split('\n') if x.startswith('s ')]
    return (st[0][2:] if st else 'UNKNOWN'), time.time() - s
with ThreadPoolExecutor(max(1, jobs)) as ex:
    res = list(ex.map(lambda cl: solve(cl[0]), leaves))
stats = dict(leaves=len(leaves), march_cubes=len(cubes), siblings=len(extra) if cubes else 1, unsat=0, sat=0, unknown=0, cube=0,
             cpu=0.0, march_wall=march_wall, max_depth=max((len(c) for c, _ in leaves), default=0))
with open(os.path.join(out, 'nodes.jsonl'), 'w') as log:
    for (c, src), (st, dt) in zip(leaves, res):
        log.write(json.dumps(dict(lits=list(c), status=st, sec=round(dt, 1), src=src)) + '\n')
        stats['cpu'] += dt
        stats[{'UNSATISFIABLE': 'unsat', 'SATISFIABLE': 'sat', 'CUBE': 'cube'}.get(st, 'unknown')] += 1
stats['cpu'] = round(stats['cpu'])
ok = stats['sat'] == 0   # an UNKNOWN leaf (T0 too short) is still a leaf: make_cert.py solves it without a limit
print(json.dumps(dict(result='UNSAT' if ok else 'NOT-UNSAT', wall=round(time.time() - t0), **stats)), flush=True)
