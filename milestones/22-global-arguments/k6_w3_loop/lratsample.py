"""LRAT size samples for 6-window threshold certificates: cold CaDiCaL 2.1.3 --lrat on the static CNF
(W3Encoding cap T-1, symmetry breaking on, the cycle cuts an incremental solve needed), raw proof capped
at 90 MB; the CNF is deleted before trimming (disk budget); every file is deleted after counting.
usage: lratsample.py 'dirs/alpha:T' ...   -> data/proof_samples.jsonl"""
import sys, os, json, time, subprocess
ME = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, ME)
import k6w3loop as L
from k6w3loop import *
sys.path.insert(0, os.path.join(ME, '..', '..', '10-window-aggregate', 'scripts'))
from gen_lean_core import trim_lrat
import wincert
CAP_KB = 90 * 1024


def parse(s):
    kk, T = s.split(':'); d, a = kk.split('/')
    al = [(6, 21) if x == '6+' else (int(x), int(x)) for x in a.split(',')]
    return survey.key(tuple(int(c) for c in d), al), int(T)


for arg in sys.argv[1:]:
    k, T = parse(arg)
    ds, al = k
    w = w3enc.window_from_dirs(list(ds))
    survey.wait_mem()
    enc = w3enc.W3Encoding(w, survey.alpha_arg(al), 4, T - 1)
    st, sel, cuts, sec = w3enc.solve(enc, 300)          # lazy cuts land in enc.clauses
    out = dict(dirs=list(ds), alpha=[list(a) for a in al], centres=len(al), T=T, lazy=st, cuts=cuts,
               variables=enc.nv, clauses=len(enc.clauses))
    if st == 'UNSAT':
        cnf = os.path.join(L.SCR, 'm.cnf'); raw = os.path.join(L.SCR, 'm.raw.lrat'); tr = os.path.join(L.SCR, 'm.lrat')
        wincert.write_cnf(enc, cnf); out['cnf_bytes'] = os.path.getsize(cnf)
        try:
            t = time.time()
            r = subprocess.run(['bash', '-c', f'ulimit -f {CAP_KB}; exec nice -n 19 {w3enc.CADICAL} -q --lrat --no-binary {cnf} {raw}'],
                               capture_output=True, text=True, timeout=900)
            out['lrat_seconds'] = round(time.time() - t, 1)
            os.remove(cnf)
            out['lrat_raw_bytes'] = os.path.getsize(raw) if os.path.exists(raw) else 0
            if r.returncode == 20:
                nl, nh, core = trim_lrat(raw, tr, len(enc.clauses))
                out.update(lrat_lemmas=nl, lrat_hints=nh, core_clauses=len(core))
            else:
                out['failed'] = f'rc {r.returncode} (raw cap 90 MB?)'
        except subprocess.TimeoutExpired:
            out['timeout'] = True
        finally:
            for p in (cnf, raw, tr):
                if os.path.exists(p):
                    os.remove(p)
    with open(L.PROOFS, 'a') as f:
        f.write(json.dumps(out) + '\n')
    print(arg, {x: out.get(x) for x in ('lazy', 'lrat_hints', 'lrat_raw_bytes', 'lrat_seconds', 'failed')}, flush=True)
