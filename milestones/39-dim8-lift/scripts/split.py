"""Adaptive binary splitting of one cube (fixed copy A of Q_k inside Q_n) on vertex literals.
A node is a list of unit literals on vertex variables s_u (DIMACS ids u+1).  Each node is solved with
CaDiCaL under a time limit T0; an unfinished node is split on the next vertex of a fixed order:
vertices outside copy 0 whose copy-0 neighbour is an end vertex of A first, then the other vertices
adjacent to A, then the rest.  The leaves form a complete binary case split (every assignment of the
branch variables is covered), so leaf UNSATs imply the cube's UNSAT.
usage: python3 split.py n c L k A.json outdir T0 jobs [extra dimacs29 flags...]"""
import sys, os, json, subprocess, time, threading
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
n, c, L, k = map(int, sys.argv[1:5]); Af = sys.argv[5]; out = sys.argv[6]; T0 = int(sys.argv[7]); jobs = int(sys.argv[8])
extra = sys.argv[9:]
os.makedirs(out, exist_ok=True)
A = set(json.load(open(Af)))
# GEN=lean: split the Lean-exported cubeCnfC4 (the certified CNF)
base = os.path.join(out, 'base.cnf')
if not os.path.exists(base):
    if os.environ.get('GEN') == 'lean':
        lean = os.path.join(HERE, '..', 'lean')
        mask = '%016x' % sum(1 << u for u in A)
        subprocess.run(['/opt/lean-4.35.0-linux/bin/lean', '--run', 'Export.lean', str(c), str(L), mask, str(len(A)), base, 'c4'],
                       check=True, capture_output=True, cwd=lean, env=dict(os.environ, LEAN_PATH=os.path.join(lean, 'build')))
    else:
        subprocess.run(['python3', os.path.join(HERE, 'dimacs29.py'), str(n), str(c), str(L), base, '--nosym', '--fix', str(k), Af] + extra,
                       check=True, capture_output=True)
hdr = open(base).readline().split(); NV, NC = int(hdr[2]), int(hdr[3])
body = open(base).read().split('\n', 1)[1]
V = 1 << n; K = 1 << k
def adeg(x): return sum(1 for i in range(k) if x ^ (1 << i) in A)
order = []
ends = [u for u in range(K, V) if any((u ^ (1 << i)) in A and adeg(u ^ (1 << i)) <= 1 for i in range(k, n))]
near = [u for u in range(K, V) if u not in ends and any((u ^ (1 << i)) < K for i in range(k, n))]
rest = [u for u in range(K, V) if u not in ends and u not in near]
order = ends + near + rest
log = open(os.path.join(out, 'nodes.jsonl'), 'a')
lock = threading.Lock()
stats = dict(leaves=0, unsat=0, sat=0, cpu=0.0)
def solve(lits):
    tag = 'n%d_%d' % (len(lits), abs(hash(tuple(lits))) % 10**9)
    f = os.path.join(out, tag + '.cnf')
    with open(f, 'w') as g:
        g.write('p cnf %d %d\n' % (NV, NC + len(lits))); g.write(body)
        for x in lits: g.write('%d 0\n' % x)
    t = time.time()
    r = subprocess.run(['cadical', '-q', '-t', str(T0), f], capture_output=True, text=True)
    os.remove(f)
    st = [x for x in r.stdout.split('\n') if x.startswith('s ')]
    return (st[0][2:] if st else 'UNKNOWN'), time.time() - t
pending = [[]]
ex = ThreadPoolExecutor(jobs)
def work(lits):
    st, dt = solve(lits)
    with lock:
        stats['cpu'] += dt
        log.write(json.dumps(dict(lits=lits, status=st, sec=round(dt, 1))) + '\n'); log.flush()
    if st == 'UNKNOWN':
        u = order[len(lits)]
        return [lits + [u + 1], lits + [-(u + 1)]]
    with lock:
        stats['leaves'] += 1
        stats['unsat' if st == 'UNSATISFIABLE' else 'sat'] += 1
    return []
t0 = time.time()
while pending:
    futs = [ex.submit(work, x) for x in pending]
    pending = [y for f in futs for y in f.result()]
    print('wave done: next', len(pending), stats, round(time.time() - t0), flush=True)
print(json.dumps(dict(result='UNSAT' if stats['sat'] == 0 else 'NOT-UNSAT', wall=round(time.time() - t0), **stats)), flush=True)
