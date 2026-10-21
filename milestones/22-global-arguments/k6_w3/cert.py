"""Certify plain-UNSAT window keys: lazy cuts (pysat CaDiCaL), then a cold CaDiCaL 2.1.3 run on the
static CNF (wincert plain encoding of the key, no symmetry breaking) with a DRAT proof, checked by
drat-trim.  CNF and proof live in the scratch directory and are deleted right after the check.
One line per key in data/certs.jsonl.   usage: cert.py KEYFILE.json   (list of [dirs, alpha])"""
import sys, os, json, time, subprocess, hashlib
from k6w3lib import *
import wincert, wincert_share as ws
CAD = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
SCR = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/k6w3'
CAP_KB = 60 * 1024
OUT = os.path.join(DATA, 'certs.jsonl')


def done():
    s = set()
    if os.path.exists(OUT):
        for l in open(OUT):
            r = json.loads(l)
            if r.get('drat_trim'):
                s.add(survey.key(tuple(r['dirs']), r['alpha']))
    return s


def certify(k, tl=600):
    survey.wait_mem()
    enc = ws.from_key(k)
    st, _, cuts, sec = ws.solve(enc, 120)
    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], k=len(k[1]), lazy=st, cuts=cuts, nv=enc.nv,
             ncl=len(enc.clauses))
    if st == 'UNSAT':
        cnf = os.path.join(SCR, 'c.cnf'); prf = os.path.join(SCR, 'c.drat')
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
        except subprocess.TimeoutExpired:
            r['timeout'] = True
        finally:
            for f in (cnf, prf):
                if os.path.exists(f):
                    os.remove(f)
    with open(OUT, 'a') as f:
        f.write(json.dumps(r) + '\n')
    print(keystr(k), {x: r.get(x) for x in ('lazy', 'cadical_s', 'drat_bytes', 'drat_trim', 'drat_trim_s')}, flush=True)
    return r


if __name__ == '__main__':
    ks = [survey.key(tuple(d), a) for d, a in json.load(open(sys.argv[1]))]
    have = done()
    for k in ks:
        if k not in have:
            certify(k)
