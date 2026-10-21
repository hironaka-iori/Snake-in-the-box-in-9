"""Sample LRAT proof sizes of UNSAT windows found by the k6 loops.

For each sampled key: lazy-cut solve (to get the static clause set with its cycle cuts), write the
CNF, one cold CaDiCaL --lrat run (file capped), and count the hints of the lemmas the empty clause
depends on (the quantity the Lean replay checks).  CNF and proof are deleted at once; nothing else
is written except one line per sample in proof_samples.jsonl.
usage: proofs.py N_PER_CLASS [seed]
"""
import sys, os, json, time, random, subprocess, array
sys.dont_write_bytecode = True
import k6loop as K
from k6loop import ws, wincert, rkey
CAD = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
CAP_KB = 120 * 1024
OUT = os.path.join(K.HERE, 'proof_samples.jsonl')


def count_hints(path, ncl):
    ids = array.array('q'); offs = array.array('q', [0]); hs = array.array('i'); last = None
    idpos = {}
    with open(path, 'rb') as f:
        for line in f:
            t = line.split()
            if len(t) > 1 and t[1] == b'd':
                continue
            i = int(t[0]); z = t.index(b'0', 1)
            idpos[i] = len(ids); ids.append(i)
            hs.extend(int(h) for h in t[z + 1:-1]); offs.append(len(hs))
            if z == 1:
                last = i
    need, stack, nh, core = set(), [last], 0, set()
    while stack:
        i = stack.pop()
        if i in need or i <= ncl:
            continue
        need.add(i); p = idpos[i]
        for h in hs[offs[p]:offs[p + 1]]:
            if h > ncl:
                stack.append(h)
            else:
                core.add(h)
        nh += offs[p + 1] - offs[p]
    return len(need), nh, len(core)


def measure(k, tl=300):
    K.wait_res()
    assert K.disk_mb() > 300 + CAP_KB / 1024, 'disk low'
    enc = ws.from_key(k)
    st, _, cuts, sec = ws.solve(enc, 120)
    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], k=len(k[1]), lazy=st, cuts=cuts, nv=enc.nv,
             ncl=len(enc.clauses), solve_s=round(sec, 2))
    if st == 'UNSAT':
        os.makedirs(K.SCR, exist_ok=True)
        cnf = os.path.join(K.SCR, 'p.cnf'); prf = os.path.join(K.SCR, 'p.lrat')
        wincert.write_cnf(enc, cnf)
        try:
            t = time.time()
            p = subprocess.run(['bash', '-c', f'ulimit -f {CAP_KB}; exec nice -n 19 {CAD} -q --lrat --no-binary {cnf} {prf}'],
                               capture_output=True, text=True, timeout=tl)
            r['lrat_s'] = round(time.time() - t, 1); r['rc'] = p.returncode
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


if __name__ == '__main__':
    n = int(sys.argv[1]); random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    files = sys.argv[3:] or [K.OPLAIN]
    rows = [json.loads(l) for fn in files for l in open(fn)]
    for kk in (5, 6):
        pool = [r for r in rows if r['kind'] == 'plain' and r['result'] == 'UNSAT' and len(r['alpha']) == kk]
        for r in random.sample(pool, min(n, len(pool))):
            measure(rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])))
