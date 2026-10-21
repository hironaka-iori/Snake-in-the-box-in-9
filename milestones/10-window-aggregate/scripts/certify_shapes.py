"""Count-free shape certificates: for each direction shape (no alpha constraints, radius 3),
CNF = wincert ball/shape clauses + known cycle cuts + share indicators + totalizer 'sum of
shares over the centres <= X'; refuted by CaDiCaL 2.1.3 (binary DRAT, --elim=false), checked by
drat-trim.  One JSON line per shape.  Independent of CP-SAT (share_enc.py builds the CNF).
  python certify_shapes.py SHAPES.jsonl X OUT.jsonl [KEEPDIR]
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from certify_share import attempt

src, X, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
keep = sys.argv[4] if len(sys.argv) > 4 else None
shapes = list(dict.fromkeys(tuple(json.loads(l)['w']['dirs']) for l in open(src)))
done = set()
if os.path.exists(out):
    done = {tuple(json.loads(l)['dirs']) for l in open(out) if json.loads(l).get('drat_trim_verified')}
for d in shapes:
    if d in done:
        continue
    k = len(d) - 1
    r = attempt(list(d), [(0, 21)] * k, X, tl=float(os.environ.get('TL', 3600)), keep=keep)
    rec = {'dirs': list(d), 'centres': k, 'X': X, 'radius': 3, 'status': r['status'],
           'drat_trim_verified': bool(r.get('verified')), 'cnf_sha256': r.get('cnf_sha256'),
           'drat_sha256': r.get('drat_sha256'), 'variables': r.get('variables'), 'clauses': r.get('clauses'),
           'cycle_cuts': r.get('shared_cuts'), 'solves': r.get('solves'), 'proof_bytes': r.get('proof_bytes'),
           'solve_sec': r.get('solve_sec'), 'check_sec': r.get('check_sec'), 'seconds': r.get('wall')}
    if r.get('cuts') is not None:
        cf = out + '.cuts.json'
        allc = json.load(open(cf)) if os.path.exists(cf) else {}
        allc[','.join(map(str, d))] = r['cuts']
        json.dump(allc, open(cf + '.tmp', 'w')); os.replace(cf + '.tmp', cf)
    if r['status'] == 'SAT':
        rec['witness_shares'] = r.get('shares')
    print(json.dumps(rec), flush=True)
    with open(out, 'a') as f:
        f.write(json.dumps(rec) + '\n')
