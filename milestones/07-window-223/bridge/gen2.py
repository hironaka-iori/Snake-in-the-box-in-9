"""Rebuild the two radius-3 (2,2,3) window CNFs with wincert.Encoding, certify with
CaDiCaL (DRUP) and trim to LRAT with drat-trim -L. Also dumps clause kinds."""
import sys, json, os, subprocess, hashlib
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/scripts')
from pysat.solvers import Cadical153
from wincert import Encoding, window_from_dirs, write_cnf, cycles_of
DRAT = '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/.build/drat-trim'
OUT = os.path.dirname(os.path.abspath(__file__)) + '/data'
os.makedirs(OUT, exist_ok=True)
CASES = {'w223_rep': [0, 1, 2, 0], 'w223_dis': [0, 1, 2, 3]}
def run(tag, dirs):
    enc = Encoding(window_from_dirs(dirs), [2, 2, 3], 3)
    while True:
        with Cadical153(bootstrap_with=enc.clauses) as s:
            if not s.solve(): break
            m = s.get_model(); sel = [v for v in enc.ball if m[enc.var[v]-1] > 0]
            cyc = cycles_of(sel); assert cyc
            for c in cyc: enc.add_cycle_cut(c)
    with Cadical153(bootstrap_with=enc.clauses, with_proof=True) as s:
        assert not s.solve(); proof = s.get_proof()
    cnf, prf, lrat = (f'{OUT}/{tag}.{e}' for e in ('cnf', 'drup', 'lrat'))
    write_cnf(enc, cnf); open(prf, 'w').write('\n'.join(proof) + '\n')
    r = subprocess.run([DRAT, cnf, prf, '-L', lrat, '-t', '600'], capture_output=True, text=True)
    assert 's VERIFIED' in r.stdout, r.stdout[-500:]
    json.dump(dict(window=enc.window, alpha=enc.alpha, radius=3, ball=enc.ball, var={str(k): v for k, v in enc.var.items()},
                   nv=enc.nv, kinds=enc.kinds, cnf_sha256=hashlib.sha256(open(cnf, 'rb').read()).hexdigest()),
              open(f'{OUT}/{tag}.meta.json', 'w'))
    print(tag, enc.nv, len(enc.clauses), hashlib.sha256(open(cnf, 'rb').read()).hexdigest())
for t in sys.argv[1:] or CASES: run(t, CASES[t])
