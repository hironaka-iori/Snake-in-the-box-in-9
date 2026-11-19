"""Cube-and-conquer by the largest copy of Q_k.
Split Q_n = Q_k x Q_{n-k} into 2^(n-k) copies of Q_k (low k coordinates).  A forest with L vertices has
a copy with >= ceil(L / 2^(n-k)) vertices; translate it to copy 0 and normalise it by B_k, so it is
one of the orbit representatives of enumk (forests of Q_k with >= that many vertices), and every other
copy has at most as many vertices.  One CNF per representative (milestone 29 encoding with levels, no
other symmetry breaking).
usage: python3 cubes.py n c L k reps.txt outdir timeout jobs
env: DIMACS_EXTRA="--allmax" (fixed copy is a largest k-subcube over all direction sets; WLOG),
     SHARD=s/N (this worker's share), STRIDE=d (sample every d-th representative).
Resumable: representatives already in outdir/results.jsonl are skipped."""
import sys, os, json, subprocess, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
n, c, L, k = map(int, sys.argv[1:5]); reps = sys.argv[5]; out = sys.argv[6]; tmo = int(sys.argv[7]); jobs = int(sys.argv[8])
os.makedirs(out, exist_ok=True)
need = -(-L // (1 << (n - k)))
R = []
for l in open(reps):
    sz, p, h = l.split(); sz = int(sz)
    if sz >= need:
        m = int(h, 16); R.append((sz, int(p), [u for u in range(1 << k) if m >> u & 1]))
print('cubes', len(R), 'need copy >=', need, flush=True)
res = os.path.join(out, 'results.jsonl')
done = set()
if os.path.exists(res):
    for l in open(res):
        done.add(json.loads(l)['idx'])
def run(i):
    if i in done: return
    sz, p, A = R[i]
    af = os.path.join(out, 'A%d.json' % i); json.dump(A, open(af, 'w'))
    cnf = os.path.join(out, 'c%d.cnf' % i)
    subprocess.run(['python3', os.path.join(HERE, 'dimacs29.py'), str(n), str(c), str(L), cnf, '--nosym', '--fix', str(k), af] + os.environ.get('DIMACS_EXTRA', '').split(),
                   check=True, capture_output=True)
    t = time.time()
    try:
        r = subprocess.run(['cadical', '-q', '-t', str(tmo), cnf], capture_output=True, text=True)
        st = [x for x in r.stdout.split('\n') if x.startswith('s ')]
        st = st[0][2:] if st else 'UNKNOWN'
    except Exception as e:
        st = 'ERR'
    os.remove(cnf)
    rec = dict(idx=i, size=sz, pieces=p, status=st, sec=round(time.time() - t, 1))
    with open(res, 'a') as f: f.write(json.dumps(rec) + '\n')
    print(rec, flush=True)
stride = int(os.environ.get('STRIDE', '1'))
shard = os.environ.get('SHARD')          # 's/N': only indices with idx % N == s
todo = list(range(0, len(R), stride))
if shard:
    s_, N_ = map(int, shard.split('/')); todo = [x for x in todo if x % N_ == s_]
# hardest first (larger fixed copies take longer), so stragglers do not end the run
todo.sort(key=lambda x: -R[x][0])
with ThreadPoolExecutor(jobs) as ex:
    list(ex.map(run, todo))
