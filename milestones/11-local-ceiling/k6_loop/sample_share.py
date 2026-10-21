"""LRAT samples of six share-threshold UNSATs of oracle_share.jsonl (static-cap CNF, cap = T - 1)."""
import sys, json, random, os, time, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proofs, k6loop as K
from k6loop import ws, wincert, rkey
rows = [json.loads(l) for l in open(K.OSHARE)]
pool = [r for r in rows if r['kind'] == 'thr' and r['result'] == 'UNSAT']
random.seed(3)
for r in random.sample(pool, 6):
    k = rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha']))
    K.wait_res(); assert K.disk_mb() > 450
    enc = ws.from_key(k, M=12, cap=r['T'] - 1)
    st, _, cuts, sec = ws.solve(enc, 120)
    out = dict(k=5, share_T=r['T'], dirs=list(k[0]), alpha=[list(a) for a in k[1]], lazy=st, nv=enc.nv, ncl=len(enc.clauses), solve_s=round(sec, 1))
    if st == 'UNSAT':
        cnf = os.path.join(K.SCR, 'p.cnf'); prf = os.path.join(K.SCR, 'p.lrat'); wincert.write_cnf(enc, cnf)
        try:
            t = time.time()
            p = subprocess.run(['bash', '-c', f'ulimit -f {proofs.CAP_KB}; exec nice -n 19 {proofs.CAD} -q --lrat --no-binary {cnf} {prf}'], capture_output=True, text=True, timeout=400)
            out.update(lrat_s=round(time.time() - t, 1), rc=p.returncode, lrat_bytes=os.path.getsize(prf))
            if p.returncode == 20:
                out['lemmas'], out['hints'], out['core'] = proofs.count_hints(prf, len(enc.clauses))
        except subprocess.TimeoutExpired:
            out['rc'] = 'timeout'
        finally:
            for f in (cnf, prf):
                if os.path.exists(f): os.remove(f)
    with open(proofs.OUT, 'a') as f: f.write(json.dumps(out) + '\n')
    print(json.dumps(out), flush=True)
