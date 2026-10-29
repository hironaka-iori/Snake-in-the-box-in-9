"""LRAT samples of the keys found UNSAT by the 233 probe (data/oracle233.jsonl.gz).

For each sampled key: lazy-cut solve (static clauses + cycle cuts), CNF to scratch, one cold
CaDiCaL --lrat run with the proof file capped at CAP_MB, hint count of the empty clause's cone
(k6_loop/proofs.py count_hints), and the CNF and proof DELETED at once.  Nothing is written
while the disk has less than 400 MB + CAP_MB free.  Stratified by kind and own solve time.
One line per sample in data/lrat233.jsonl.

  nice -n 19 python lrat233.py N [seed]
"""
import sys, os, json, time, random, subprocess, gzip
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), '25-k7-234'))
import k7                    # noqa: E402
sys.path.insert(0, os.path.join(k7.MS, '11-local-ceiling', 'k6_loop'))
from proofs import count_hints, CAD   # noqa: E402

OUT = os.path.join(HERE, 'data', 'lrat233.jsonl')
ORACLE = os.path.join(HERE, 'data', 'oracle233.jsonl.gz')
SCR = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/probe233/lrat'
CAP_MB = 40


def disk_mb():
    st = os.statvfs('/')
    return st.f_bavail * st.f_frsize / 2 ** 20


def measure(k, sec, tl=600):
    k7.guard()
    while disk_mb() < 400 + CAP_MB + 10:
        print('disk low, waiting', flush=True); time.sleep(60)
    enc = k7.encoding(k)
    t = time.time()
    res, _, cuts = k7.W.decide(enc, certify=False)
    r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), seconds=sec, resolve_s=round(time.time() - t, 3),
             result=res, cuts=cuts, nv=enc.nv, ncl=len(enc.clauses))
    if res == 'UNSAT':
        os.makedirs(SCR, exist_ok=True)
        cnf = os.path.join(SCR, 'p.cnf'); prf = os.path.join(SCR, 'p.lrat')
        k7.W.write_cnf(enc, cnf)
        try:
            t = time.time()
            p = subprocess.run(['bash', '-c', f'ulimit -f {CAP_MB * 1024}; exec nice -n 19 {CAD} -q --lrat --no-binary {cnf} {prf}'],
                               capture_output=True, text=True, timeout=tl)
            r['lrat_s'] = round(time.time() - t, 2); r['rc'] = p.returncode
            r['lrat_bytes'] = os.path.getsize(prf) if os.path.exists(prf) else None
            if p.returncode == 20:
                r['lemmas'], r['hints'], r['core'] = count_hints(prf, len(enc.clauses))
        except subprocess.TimeoutExpired:
            r['rc'] = 'timeout'
        finally:
            for f in (cnf, prf):
                if os.path.exists(f):
                    os.remove(f)
    with open(OUT, 'a') as f:
        f.write(json.dumps(r) + '\n')
    print(json.dumps(r), flush=True)
    return r


def main():
    n = int(sys.argv[1]); random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
    pool = {}
    for l in gzip.open(ORACLE, 'rt'):
        r = json.loads(l)
        if r['result'] == 'UNSAT' and r.get('radius', 4) == 4 and r['kind'] in ('H', 'F', 'k6'):
            pool[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r['seconds']
    done = set()
    if os.path.exists(OUT):
        done = {(r['kind'], tuple(r['dirs']), tuple(r['syms'])) for r in map(json.loads, open(OUT))}
    strata = {}
    for k, s in sorted(pool.items()):
        if k in done:
            continue
        strata.setdefault((k[0], 0 if s < 0.05 else 1 if s < 0.15 else 2 if s < 0.5 else 3), []).append(k)
    tot = sum(len(v) for v in strata.values())
    pick = []
    for st, v in sorted(strata.items()):
        pick += random.sample(v, min(len(v), max(2, round(n * len(v) / tot))))
    print({str(k): len(v) for k, v in sorted(strata.items())}, len(pick), flush=True)
    for k in pick:
        measure(k, pool[k])


if __name__ == '__main__':
    main()
