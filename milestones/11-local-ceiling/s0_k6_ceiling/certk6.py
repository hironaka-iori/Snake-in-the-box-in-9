"""Certify an UNSAT window: lazy cuts, then the CaDiCaL binary with a DRAT proof checked by drat-trim.
The CNF and proof are deleted right after the check.  usage: certk6.py plain|thr dirs radius [T|-] [alpha, e.g. 3,6-21,3,3,6-21,3]"""
import sys, os, json, time, subprocess, hashlib
sys.dont_write_bytecode = True
from k6lib import wincert, ws
HERE = os.path.dirname(os.path.abspath(__file__))
CAD = os.environ.get('CADICAL', '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical')
CAP_KB = 90 * 1024

def free_mb():
    s = os.statvfs('/'); return s.f_bavail * s.f_frsize / 2**20

def certify(kind, ds, radius, T=None, M=12, tl=600, alpha=None):
    k = len(ds) - 1; w = wincert.window_from_dirs(list(ds)); al = alpha or [4] * k
    enc = wincert.Encoding(w, al, radius) if kind == 'plain' else ws.ShareEncoding(w, al, radius, M, T - 1)
    st, _, cuts, sec = ws.solve(enc, tl)
    r = dict(kind=kind, dirs=list(ds), alpha=[a if isinstance(a, int) else list(a) for a in al], k=k, radius=radius, T=T, M=M, lazy=st, cuts=cuts, nv=enc.nv, ncl=len(enc.clauses))
    if st == 'UNSAT':
        assert free_mb() > 400, 'disk low'
        cnf = os.path.join(HERE, 'c.cnf'); prf = os.path.join(HERE, 'c.drat')
        wincert.write_cnf(enc, cnf)
        r['cnf_sha256'] = hashlib.sha256(open(cnf, 'rb').read()).hexdigest()
        try:
            t = time.time()
            p = subprocess.run(['bash', '-c', f'ulimit -f {CAP_KB}; exec nice -n 19 {CAD} -q --no-binary {cnf} {prf}'],
                               capture_output=True, text=True, timeout=tl)
            r['cadical_rc'] = p.returncode; r['cadical_s'] = round(time.time() - t, 1)
            r['drat_bytes'] = os.path.getsize(prf) if os.path.exists(prf) else None
            if p.returncode == 20:
                t = time.time()
                q = subprocess.run(['nice', '-n', '19', wincert.ensure_drat(), cnf, prf, '-t', str(tl)],
                                   capture_output=True, text=True, timeout=tl + 60)
                r['drat_trim'] = 's VERIFIED' in q.stdout; r['drat_trim_s'] = round(time.time() - t, 1)
        finally:
            for f in (cnf, prf):
                if os.path.exists(f): os.remove(f)
    with open(os.path.join(HERE, 'certs.jsonl'), 'a') as f:
        f.write(json.dumps(r) + '\n')
    print(json.dumps(r), flush=True)
    return r

if __name__ == '__main__':
    certify(sys.argv[1], tuple(int(x) for x in sys.argv[2].split(',')), int(sys.argv[3]),
            int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != '-' else None,
            alpha=[int(x) if '-' not in x else tuple(int(y) for y in x.split('-')) for x in sys.argv[5].split(',')]
            if len(sys.argv) > 5 else None)
