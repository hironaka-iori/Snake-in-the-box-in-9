"""Re-verify the count-free share certificates from scratch.

For every line of a shape-certificate file (data/share/final_*.jsonl): regenerate the CNF from the
direction shape, the bound X and the recorded cycle cuts (regen_cnf.py's construction), require
its sha256 to equal the recorded cnf_sha256, solve it with CaDiCaL writing a DRAT proof, and check
the proof with the vendored drat-trim.

  python3 verify_share_certs.py ../data/share/final_a_X20.jsonl [--jobs 2] [--out summary.json]
"""
import argparse, hashlib, json, os, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from share_enc import ShareEncoding, window_from_dirs  # noqa: E402
from wincert import write_cnf, ensure_drat  # noqa: E402
from certify_share import CADICAL_BIN  # noqa: E402


def check(rec, cuts):
    dirs, X = rec['dirs'], rec['X']
    k = len(dirs) - 1
    t = time.time()
    with tempfile.TemporaryDirectory() as td:
        cnf, prf = os.path.join(td, 'f.cnf'), os.path.join(td, 'f.drat')
        enc = ShareEncoding(window_from_dirs(dirs), [(0, 21)] * k, 3, X, counter='stot', exact=True)
        for c in cuts[','.join(map(str, dirs))]:
            enc.add_cycle_cut(c)
        write_cnf(enc, cnf)
        sha = hashlib.sha256(open(cnf, 'rb').read()).hexdigest()
        if sha != rec['cnf_sha256']:
            return dict(dirs=dirs, ok=False, why='cnf sha256 mismatch')
        r = subprocess.run([CADICAL_BIN, '--elim=false', '-q', cnf, prf], capture_output=True, text=True)
        if r.returncode != 20:
            return dict(dirs=dirs, ok=False, why=f'cadical exit {r.returncode}')
        r = subprocess.run([ensure_drat(), cnf, prf, '-t', '20000'], capture_output=True, text=True)
        ok = 's VERIFIED' in r.stdout
        return dict(dirs=dirs, X=X, ok=ok, why='' if ok else 'drat-trim did not verify',
                    seconds=round(time.time() - t, 1))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('certs')
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--out')
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.certs) if l.strip()]
    cuts = json.load(open(a.certs + '.cuts.json'))
    ensure_drat()
    with ThreadPoolExecutor(a.jobs) as pool:
        res = []
        for r in pool.map(lambda rec: check(rec, cuts), recs):
            res.append(r)
            print(json.dumps(r), flush=True)
    bad = [r for r in res if not r['ok']]
    summary = dict(file=os.path.basename(a.certs), shapes=len(res), verified=len(res) - len(bad),
                   failed=len(bad), X=sorted({r['X'] for r in recs}))
    print(json.dumps(summary))
    if a.out:
        json.dump(dict(summary, results=res), open(a.out, 'w'), indent=1)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
