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


def one(arg):
    """One window.  The proof-logging solver decides the window directly; most windows need no
    cycle cut, and then this single solve also gives the proof (the earlier version always solved
    twice).  Windows that needed cuts are proved again from cold on the final clause set."""
    dirs, alpha, radius, drat, keep = arg
    t = time.time()
    al = [lo if lo == hi else (lo, hi) for lo, hi in alpha]
    enc = Encoding(window_from_dirs(dirs), al, radius)
    cuts = 0
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
        proof = s.get_proof()
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
            'variables': enc.nv, 'clauses': len(enc.clauses), 'cycle_cuts': cuts,
            'proof_lines': len(proof), 'drat_trim_verified': ok, 'cnf_sha256': shas['cnf'],
            'drup_sha256': shas['drup'], 'seconds': round(time.time() - t, 2)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--set', required=True)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--out', default=os.path.join(HERE, '..', 'data', 'direction_certificates.json'))
    ap.add_argument('--keep-files', action='store_true',
                    help='store the gzipped CNF and proof of every window (the index keeps their SHA-256 either way; '
                         'thousands of cap-7 proofs take tens of GB and are regenerated deterministically)')
    a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    drat = ensure_drat()
    spec = json.load(open(a.set))
    jobs = [(e['dirs'], [tuple(r) for r in e['alpha']], a.radius, drat, a.keep_files) for e in spec['exclusions']]
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
    with Pool(a.workers) as p:
        for rec in p.imap_unordered(one, todo):
            print(rec.get('case', rec['dirs']), rec['drat_trim_verified'], rec.get('seconds'), flush=True)
            results.append(rec)
            # atomic replace: a machine restart during the write must not truncate the index
            tmp = a.out + '.tmp'
            with open(tmp, 'w') as f:
                json.dump({'scope': 'DRAT-checked UNSAT of explicit local CNFs (radius-three ball model); '
                                    'not Lean-checked.', 'source_set': os.path.basename(a.set),
                           'drat_trim_source_sha256': DRAT_SOURCE_SHA256, 'cases': results}, f, indent=1)
            os.replace(tmp, a.out)
    bad = [r for r in results if not r['drat_trim_verified']]
    print('verified', len(results) - len(bad), 'failed', len(bad))


if __name__ == '__main__':
    main()
