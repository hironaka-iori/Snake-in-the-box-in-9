"""Measured LRAT sizes (trimmed full-proof hints, CaDiCaL --lrat --no-binary --unsat, as cert233.core_plain)
of a stratified sample of the 58,817 K7R34C7W16 window exclusions (relaxed-keller milestone 10 set).
usage: lratsample.py MINIMAL_SET.json INDEX.json OUT.jsonl N [workers] [radius]
The sample is stratified by the index's DRUP proof_lines (N equal-count strata, one random window each).
"""
import os, sys, json, random, tempfile, time, shutil
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
import wincert, gen_lean_core as GC


def one(arg):
    c, radius = arg
    t0 = time.time()
    al = [lo if lo == hi else (lo, hi) for lo, hi in c['alpha']]
    enc = wincert.Encoding(wincert.window_from_dirs(c['dirs']), al, radius or c['radius'])
    st, _, ncuts = wincert.decide(enc, certify=False)
    out = dict(case=c['case'], radius=radius or c['radius'], proof_lines=c['proof_lines'], drat_s=c['seconds'],
               status=st, cuts=ncuts)
    if st != 'UNSAT':
        return out
    td = tempfile.mkdtemp(prefix='lrs_', dir=os.environ.get('LRS_TMP'))
    try:
        cnf = os.path.join(td, 'w.cnf')
        wincert.write_cnf(enc, cnf)
        t1 = time.time()
        nl, nh, desc, ids = GC.best_cadical_proof(cnf, os.path.join(td, 'f'), shutil.which('cadical'), [1],
                                                  portfolio=[['--unsat']], rounds=1)
        out.update(lemmas=nl, est_hints=nh, core=len(ids), decide_s=round(t1 - t0, 2), lrat_s=round(time.time() - t1, 2))
    finally:
        shutil.rmtree(td, ignore_errors=True)
    return out


if __name__ == '__main__':
    mset, idxf, outf, N = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    nw = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    radius = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    idx = {(tuple(c['dirs']), tuple(map(tuple, c['alpha']))): c for c in json.load(open(idxf))['cases']}
    cs = [idx[(tuple(e['dirs']), tuple(map(tuple, e['alpha'])))] for e in json.load(open(mset))['exclusions']]
    cs.sort(key=lambda c: c['proof_lines'])
    rnd = random.Random(230)
    n = len(cs); pick = [cs[rnd.randrange(i * n // N, (i + 1) * n // N)] for i in range(N)]
    pick.reverse()                     # big ones first
    with Pool(nw) as p:
        for r in p.imap_unordered(one, [(c, radius) for c in pick]):
            with open(outf, 'a') as f:
                f.write(json.dumps(r) + '\n')
            print(r, flush=True)
