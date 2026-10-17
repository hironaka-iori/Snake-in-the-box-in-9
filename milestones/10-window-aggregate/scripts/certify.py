"""DRAT certificates for the window exclusions assumed by Aggregate242Conditional.

Each case is an explicit CNF (wincert.Encoding plus the cycle cuts found
while refuting it).  CaDiCaL emits a DRUP proof which is checked by the
repository's vendored drat-trim.  Only the CNF semantics, not the proof
search, needs trust; see README for the remaining geometric bridge.

  python certify.py   (writes ../certificates/*.gz and ../data/certificates.json)
"""
import gzip, hashlib, json, os, subprocess, tempfile, time
from pysat.solvers import Cadical153
from wincert import Encoding, decide, window_from_dirs, write_cnf, ensure_drat, DRAT_SOURCE_SHA256

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'certificates')
SHAPES3 = {'repeated': (0, 1, 2, 0), 'distinct': (0, 1, 2, 3)}
SHAPES4 = {'s01203': (0, 1, 2, 0, 3), 's01230': (0, 1, 2, 3, 0), 's01234': (0, 1, 2, 3, 4)}
PATTERNS = {'223': (2, 2, 3), '224': (2, 2, 4), '232': (2, 3, 2), '323': (3, 2, 3), '41c': (4, 1, (4, 6)),
            '2423': (2, 4, 2, 3)}


def main():
    os.makedirs(OUT, exist_ok=True)
    records = []
    for name, pat in PATTERNS.items():
        for orient, pp in (('fwd', pat), ('rev', tuple(pat[::-1]))):
            if orient == 'rev' and pp == pat:
                continue
            for shape, ds in (SHAPES3 if len(pat) == 3 else SHAPES4).items():
                t = time.time()
                enc = Encoding(window_from_dirs(ds), list(pp), 3)
                st, _, cuts = decide(enc, certify=False)
                assert st == 'UNSAT', (name, orient, shape, st)
                tag = f'{name}_{orient}_{shape}'
                with tempfile.TemporaryDirectory() as td:
                    cnf, prf = os.path.join(td, tag + '.cnf'), os.path.join(td, tag + '.drup')
                    write_cnf(enc, cnf)
                    with Cadical153(bootstrap_with=enc.clauses, with_proof=True) as s:
                        assert not s.solve()
                        proof = s.get_proof()
                    open(prf, 'w').write('\n'.join(proof) + '\n')
                    r = subprocess.run([ensure_drat(), cnf, prf, '-t', '1200'], capture_output=True, text=True)
                    for f in (cnf, prf):
                        data = open(f, 'rb').read()
                        with gzip.GzipFile(os.path.join(OUT, os.path.basename(f) + '.gz'), 'wb', mtime=0) as g:
                            g.write(data)
                    cnf_sha = hashlib.sha256(open(cnf, 'rb').read()).hexdigest()
                    prf_sha = hashlib.sha256(open(prf, 'rb').read()).hexdigest()
                kinds = {}
                for k in enc.kinds:
                    k = k.split('@')[0]; kinds[k] = kinds.get(k, 0) + 1
                rec = dict(case=tag, directions=list(ds), window=window_from_dirs(ds),
                           alpha=[list(a) if isinstance(a, tuple) else a for a in pp], radius=3,
                           endpoint_budget=2, variables=enc.nv, clauses=len(enc.clauses),
                           cycle_cuts=cuts, clause_kinds=kinds, proof_lines=len(proof),
                           drat_trim_verified='s VERIFIED' in r.stdout, cnf_sha256=cnf_sha,
                           drup_sha256=prf_sha, seconds=round(time.time() - t, 2))
                print(tag, rec['drat_trim_verified'], cuts, len(proof), flush=True)
                records.append(rec)
    json.dump({'scope': 'DRAT-checked UNSAT of explicit local CNFs; not Lean-checked.',
               'drat_trim_source_sha256': DRAT_SOURCE_SHA256,
               'cases': records}, open(os.path.join(HERE, '..', 'data', 'certificates.json'), 'w'), indent=1)
    assert all(r['drat_trim_verified'] for r in records)


if __name__ == '__main__':
    main()
