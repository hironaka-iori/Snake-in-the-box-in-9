"""LRAT samples of F8/H9 keys (and the hint count the Lean replay would check).

For each sampled UNSAT key of data/oracle_k7.jsonl.gz: lazy-cut solve (the static clause set
with its cycle cuts), write the CNF to the scratch directory, one cold CaDiCaL --lrat run
(proof file capped at 100 MB), count the hints the empty clause depends on
(k6_loop/proofs.py count_hints), and DELETE the CNF and the proof at once.  One line per
sample in data/lrat_samples.jsonl.  Stratified by the key's own solve time.

  nice -n 19 python lrat_samples.py N [seed] [--keys data/keys_TAG.json.gz]
"""
import sys, os, json, time, random, subprocess, gzip
sys.dont_write_bytecode = True
import k7
sys.path.insert(0, os.path.join(k7.MS, '11-local-ceiling', 'k6_loop'))
from proofs import count_hints, CAD   # noqa: E402

OUT = os.path.join(k7.HERE, 'data', 'lrat_samples.jsonl')
CAP_KB = 100 * 1024


def measure(k, sec, tl=600):
    k7.guard()
    st = os.statvfs('/')
    assert st.f_bavail * st.f_frsize / 2 ** 20 > 500 + CAP_KB / 1024, 'disk low'
    enc = k7.encoding(k)
    t = time.time()
    res, _, cuts = k7.W.decide(enc, certify=False)
    r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), seconds=sec, resolve_s=round(time.time() - t, 3),
             result=res, cuts=cuts, nv=enc.nv, ncl=len(enc.clauses))
    if res == 'UNSAT':
        os.makedirs(k7.SCR, exist_ok=True)
        cnf = os.path.join(k7.SCR, 'p.cnf'); prf = os.path.join(k7.SCR, 'p.lrat')
        k7.W.write_cnf(enc, cnf)
        try:
            t = time.time()
            p = subprocess.run(['bash', '-c', f'ulimit -f {CAP_KB}; exec nice -n 19 {CAD} -q --lrat --no-binary {cnf} {prf}'],
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
    n = int(sys.argv[1]); random.seed(int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith('-') else 7)
    O = k7.Oracle()
    pool = [k for k, s in O.st.items() if s == 'UNSAT']
    if '--keys' in sys.argv:
        d = json.load(gzip.open(sys.argv[sys.argv.index('--keys') + 1], 'rt'))
        want = {(k[0], tuple(k[1]), tuple(k[2])) for k in d['keys'] if k[0] != 'k6'}
        pool = [k for k in pool if k in want]
    done = set()
    if os.path.exists(OUT):
        done = {(r['kind'], tuple(r['dirs']), tuple(r['syms'])) for r in map(json.loads, open(OUT))}
    pool = sorted(k for k in pool if k not in done)
    strata = {}
    for k in pool:
        s = O.sec[k]
        strata.setdefault((k[0], 0 if s < 0.08 else 1 if s < 0.15 else 2 if s < 0.4 else 3), []).append(k)
    tot = sum(len(v) for v in strata.values())
    pick = []
    for st, v in sorted(strata.items()):
        pick += random.sample(v, min(len(v), max(1, round(n * len(v) / tot))))
    print({str(k): len(v) for k, v in sorted(strata.items())}, len(pick), flush=True)
    for k in pick:
        measure(k, O.sec[k])


if __name__ == '__main__':
    main()
