"""DRAT certificates for a list of direction-aware window exclusions.

Reads a minimal-set JSON (from minimize.py), builds the explicit CNF of each
window with wincert.Encoding (lazy cycle cuts included), refutes it with
CaDiCaL, verifies the DRUP proof with the vendored drat-trim, and stores the
gzipped CNF/proof under ../certificates/direction/.  Keys are canonical up to
coordinate relabelling and reversal, so one certificate per key suffices.

  python certify_direction.py --set ../data/minimal_L6_k4_K5.json --workers 4
"""
import argparse, gzip, hashlib, json, os, subprocess, tempfile, time
from multiprocessing import Pool
from pysat.solvers import Cadical153
from wincert import Encoding, decide, window_from_dirs, write_cnf, ensure_drat, DRAT_SOURCE_SHA256, cycles_of

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'certificates', 'direction')


def tag_of(dirs, alpha):
    return 'd' + ''.join(map(str, dirs)) + '_a' + '_'.join(
        f'{lo}' if lo == hi else f'{lo}-{hi}' for lo, hi in alpha)


# Cycle cuts found so far, per (direction shape, radius).  A cut forbids one cycle of the ball
# from being entirely selected; a snake induces a path, so every cut is valid for every window
# of that shape (same ball, same variables).  Adding the known cuts before the first solve lets
# most windows finish without the solve-and-cut loop and without the cold re-proof.
CUTS = {}


def init_cuts(path):
    if path and os.path.exists(path):
        for k, v in json.load(open(path)).items():
            dirs, radius = k.rsplit('/', 1)
            CUTS[(tuple(int(x) for x in dirs.split(',')), int(radius))] = [tuple(c) for c in v]


def one(arg):
    """One window.  The proof-logging solver decides the window directly, with the cycle cuts
    already known for its shape added up front; most windows need no further cut, and then this
    single solve also gives the proof.  Windows that needed new cuts are proved again from cold
    on the final clause set."""
    dirs, alpha, radius, drat, keep = arg
    t = time.time()
    al = [lo if lo == hi else (lo, hi) for lo, hi in alpha]
    enc = Encoding(window_from_dirs(dirs), al, radius)
    key = (tuple(dirs), radius)
    known = CUTS.setdefault(key, [])
    for c in known:
        enc.add_cycle_cut(c)
    shared = len(known)
    cuts, found = 0, []
    with Cadical153(bootstrap_with=enc.clauses, with_proof=True) as s:
        while s.solve():
            model = s.get_model()
            sel = [v for v in enc.ball if model[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc or cuts > 10000:
                return {'dirs': dirs, 'alpha': alpha, 'status': 'SAT' if not cyc else 'UNKNOWN',
                        'drat_trim_verified': False}
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
                s.add_clause(enc.clauses[-1])
                found.append(tuple(sorted(c)))
        proof = s.get_proof()
    have = set(known)
    known.extend(c for c in found if c not in have)
    if cuts:
        # clauses added after a solve can force CaDiCaL to restore clauses that variable
        # elimination already deleted in the proof; drat-trim rejects such proofs, so windows
        # that needed cuts get a cold proof solve of the final clause set
        with Cadical153(bootstrap_with=enc.clauses, with_proof=True) as s:
            assert not s.solve()
            proof = s.get_proof()
    tag = tag_of(dirs, alpha)
    with tempfile.TemporaryDirectory() as td:
        cnf, prf = os.path.join(td, tag + '.cnf'), os.path.join(td, tag + '.drup')
        write_cnf(enc, cnf)
        with open(prf, 'w') as f:
            f.write('\n'.join(proof) + '\n')
        r = subprocess.run([drat, cnf, prf, '-t', '3600'], capture_output=True, text=True)
        ok = 's VERIFIED' in r.stdout
        shas = {}
        for f in (cnf, prf):
            data = open(f, 'rb').read()
            shas[os.path.splitext(f)[1][1:]] = hashlib.sha256(data).hexdigest()
            if keep:
                with gzip.GzipFile(os.path.join(OUT, os.path.basename(f) + '.gz'), 'wb', mtime=0) as g:
                    g.write(data)
    return {'case': tag, 'dirs': dirs, 'alpha': alpha, 'radius': radius, 'endpoint_budget': 2,
            'variables': enc.nv, 'clauses': len(enc.clauses), 'cycle_cuts': cuts, 'shared_cuts': shared,
            'new_cuts': found,
            'proof_lines': len(proof), 'drat_trim_verified': ok, 'cnf_sha256': shas['cnf'],
            'drup_sha256': shas['drup'], 'seconds': round(time.time() - t, 2)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--set', required=True)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--out', default=os.path.join(HERE, '..', 'data', 'direction_certificates.json'))
    ap.add_argument('--cuts', default=os.path.join(HERE, '..', 'data', 'cycle_cuts.json'),
                    help='store of cycle cuts per direction shape, shared by the workers and kept across runs')
    ap.add_argument('--keep-files', action='store_true',
                    help='store the gzipped CNF and proof of every window (the index keeps their SHA-256 either way; '
                         'thousands of cap-7 proofs take tens of GB and are regenerated deterministically)')
    a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    drat = ensure_drat()
    spec = json.load(open(a.set))
    # an exclusion may name the radius of the ball that refutes it (two-level oracle)
    jobs = [(e['dirs'], [tuple(r) for r in e['alpha']], e.get('radius', a.radius), drat, a.keep_files)
            for e in spec['exclusions']]
    # largest windows first for better load balance
    jobs.sort(key=lambda j: -len(j[0]))
    done = {}
    if os.path.exists(a.out):
        for c in json.load(open(a.out))['cases']:
            if c.get('drat_trim_verified'):
                done[(tuple(c['dirs']), tuple(map(tuple, c['alpha'])))] = c
    todo = [j for j in jobs if (tuple(j[0]), tuple(j[1])) not in done]
    print('cases', len(jobs), 'already verified', len(done), 'to do', len(todo), flush=True)
    results = list(done.values())
    cut_file = a.cuts
    init_cuts(cut_file)
    with Pool(a.workers, initializer=init_cuts, initargs=(cut_file,)) as p:
        for n, rec in enumerate(p.imap_unordered(one, todo)):
            print(rec.get('case', rec['dirs']), rec['drat_trim_verified'], rec.get('seconds'), flush=True)
            new = rec.pop('new_cuts', [])
            if new:
                known = CUTS.setdefault((tuple(rec['dirs']), rec['radius']), [])
                have = set(known)
                known.extend(c for c in new if c not in have)
            if cut_file and (new or n % 50 == 0):
                tmp = cut_file + '.tmp'
                with open(tmp, 'w') as f:
                    json.dump({','.join(map(str, d)) + '/' + str(r): v for (d, r), v in CUTS.items() if v}, f)
                os.replace(tmp, cut_file)
            results.append(rec)
            # atomic replace: a machine restart during the write must not truncate the index
            tmp = a.out + '.tmp'
            with open(tmp, 'w') as f:
                json.dump({'scope': 'DRAT-checked UNSAT of explicit local CNFs (radius-three or radius-four ball model, per case); '
                                    'not Lean-checked.', 'source_set': os.path.basename(a.set),
                           'drat_trim_source_sha256': DRAT_SOURCE_SHA256, 'cases': results}, f, indent=1)
            os.replace(tmp, a.out)
    bad = [r for r in results if not r['drat_trim_verified']]
    print('verified', len(results) - len(bad), 'failed', len(bad))


if __name__ == '__main__':
    main()
