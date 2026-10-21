"""DRAT certificates for lower bounds on the sum of empty-square shares over a window's centres.

For a window (dirs, alpha) and bound B, builds share_enc.ShareEncoding (wincert.Encoding +
share terms + counter for sum <= B), adds the cycle cuts known for the shape, decides it with
CaDiCaL (proof logging) with lazy cycle cuts, and checks the DRUP proof with drat-trim.  UNSAT
for B certifies LB = B + 1.  Each attempt runs in a child process with a wall-clock limit and an
address-space limit; the parent only waits.

  python certify_share.py --dirs 0 1 2 3 4 2 1 5 --alpha 5 3 5 5 5 3 5 --B 25
  python certify_share.py --dirs ... --alpha ... --search --tl 120     # largest certifiable LB
"""
import argparse, json, multiprocessing as mp, os, resource, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from share_enc import ShareEncoding, share_of, window_from_dirs  # noqa: E402
from wincert import cycles_of, write_cnf, ensure_drat  # noqa: E402
from pysat.solvers import Cadical153, Cadical195  # noqa: E402

REPO_CUTS = os.path.join(HERE, '..', 'data', 'cycle_cuts.json')
LOCAL_CUTS = os.path.join(HERE, 'share_cuts.json')
TMP = os.path.join(HERE, 'tmp')
SOLVERS = {'cadical153': Cadical153, 'cadical195': Cadical195}
CADICAL_BIN = '/root/.elan/toolchains/leanprover--lean4---v4.19.0/bin/cadical'   # CaDiCaL 2.1.3


MAX_PROOF = int(os.environ.get('MAX_PROOF_MB', 700)) * 2**20


def _run_capped(cmd, prf):
    """subprocess.run, but kill the solver when the proof file exceeds MAX_PROOF bytes."""
    with tempfile.TemporaryFile('w+') as out:
        p = subprocess.Popen(cmd, stdout=out, stderr=subprocess.DEVNULL, text=True)
        while True:
            try:
                p.wait(2)
                break
            except subprocess.TimeoutExpired:
                if prf and os.path.exists(prf) and os.path.getsize(prf) > MAX_PROOF:
                    p.kill(); p.wait()
                    return None
        out.seek(0)
        return subprocess.CompletedProcess(cmd, p.returncode, out.read(), '')


def _attempt_bin(dirs, alpha, B, radius, counter, exact, check, keep):
    """Same as _attempt with the CaDiCaL 2.1.3 executable: the proof goes to a file in binary
    DRAT (no proof held in memory).  Lazy cycle cuts: every solve is cold on the current CNF, so
    the last (UNSAT) run's proof is a proof of exactly the CNF that is checked."""
    t0 = time.time()
    al = [a[0] if a[0] == a[1] else tuple(a) for a in alpha]
    enc = ShareEncoding(window_from_dirs(dirs), al, radius, B, counter=counter, exact=exact)
    known = load_cuts(dirs, radius)
    for c in known:
        enc.add_cycle_cut(c)
    found, nsolve = [], 0
    os.makedirs(TMP, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=TMP, prefix=f'a{os.getpid()}_') as td:
        cnf, prf = os.path.join(td, 'f.cnf'), os.path.join(td, 'f.drat')
        while True:
            write_cnf(enc, cnf)
            cmd = [CADICAL_BIN, '-q'] + os.environ.get('CADICAL_OPTS', '--elim=false').split() + [cnf] + ([prf, '--binary=true'] if check else [])
            r = _run_capped(cmd, prf if check else None)
            nsolve += 1
            if r is None:
                return {'status': 'PROOF_TOO_BIG', 'new_cuts': found}
            if r.returncode == 20:
                break
            assert r.returncode == 10, (r.returncode, r.stderr[-500:])
            model = set()
            for line in r.stdout.splitlines():
                if line.startswith('v '):
                    model.update(int(x) for x in line[2:].split() if int(x) > 0)
            sel = [v for v in enc.ball if enc.var[v] in model]
            cyc = cycles_of(sel)
            if not cyc:
                per = [share_of(sel, c) for c in enc.window[1:-1]]
                mper = enc.model_shares([v if v in model else -v for v in range(1, enc.nv + 1)])
                return {'status': 'SAT', 'shares': per, 'sum': sum(per), 'model_shares': mper,
                        'new_cuts': found, 'sec': round(time.time() - t0, 2), 'sel': sel}
            for c in cyc:
                enc.add_cycle_cut(c); found.append(tuple(sorted(c)))
        tsolve = time.time() - t0
        rec = {'status': 'UNSAT', 'new_cuts': found, 'solves': nsolve, 'cuts': [list(c) for c in known + found], 'shared_cuts': len(known),
               'variables': enc.nv, 'clauses': len(enc.clauses), 'share_clauses': enc.n_share - enc.n_base,
               'counter_clauses': len(enc.clauses) - enc.n_share - len(known) - len(found)}
        if not check:
            rec['sec'] = round(tsolve, 2)
            return rec
        pbytes = os.path.getsize(prf)
        import hashlib
        rec['cnf_sha256'] = hashlib.sha256(open(cnf, 'rb').read()).hexdigest()
        rec['drat_sha256'] = hashlib.sha256(open(prf, 'rb').read()).hexdigest()
        t1 = time.time()
        r = subprocess.run([ensure_drat(), cnf, prf, '-t', '20000'], capture_output=True, text=True)
        tcheck = time.time() - t1
        if keep:
            import gzip, shutil
            os.makedirs(keep, exist_ok=True)
            tag = 'd' + ''.join(map(str, dirs)) + '_a' + '_'.join(f'{a[0]}' if a[0] == a[1] else f'{a[0]}-{a[1]}' for a in alpha) + f'_B{B}'
            for f in (cnf, prf):
                with open(f, 'rb') as fi, gzip.open(os.path.join(keep, tag + os.path.splitext(f)[1] + '.gz'), 'wb') as fo:
                    shutil.copyfileobj(fi, fo)
    rec.update({'verified': 's VERIFIED' in r.stdout, 'proof_bytes': pbytes,
                'solve_sec': round(tsolve, 2), 'check_sec': round(tcheck, 2), 'sec': round(time.time() - t0, 2)})
    return rec


def load_cuts(dirs, radius):
    out = []
    for p in (REPO_CUTS, LOCAL_CUTS):
        if os.path.exists(p):
            out += [tuple(c) for c in json.load(open(p)).get(','.join(map(str, dirs)) + '/' + str(radius), [])]
    return list(dict.fromkeys(out))


def save_cuts(dirs, radius, new):
    if not new:
        return
    d = json.load(open(LOCAL_CUTS)) if os.path.exists(LOCAL_CUTS) else {}
    k = ','.join(map(str, dirs)) + '/' + str(radius)
    have = {tuple(c) for c in d.get(k, [])}
    d.setdefault(k, []).extend(list(c) for c in new if tuple(c) not in have)
    json.dump(d, open(LOCAL_CUTS + '.tmp', 'w')); os.replace(LOCAL_CUTS + '.tmp', LOCAL_CUTS)


def _attempt(dirs, alpha, B, radius, counter, exact, solver, check, keep):
    t0 = time.time()
    al = [a[0] if a[0] == a[1] else tuple(a) for a in alpha]
    enc = ShareEncoding(window_from_dirs(dirs), al, radius, B, counter=counter, exact=exact)
    known = load_cuts(dirs, radius)
    for c in known:
        enc.add_cycle_cut(c)
    S = SOLVERS[solver]
    found = []
    with S(bootstrap_with=enc.clauses, with_proof=check) as s:
        while s.solve():
            model = s.get_model()
            sel = [v for v in enc.ball if model[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc:
                per = [share_of(sel, c) for c in enc.window[1:-1]]
                mper = enc.model_shares(model)
                return {'status': 'SAT', 'shares': per, 'sum': sum(per), 'model_shares': mper,
                        'new_cuts': found, 'sec': round(time.time() - t0, 2), 'sel': sel}
            for c in cyc:
                enc.add_cycle_cut(c); found.append(tuple(sorted(c)))
                s.add_clause(enc.clauses[-1])
        proof = s.get_proof() if check else None
    tsolve = time.time() - t0
    rec = {'status': 'UNSAT', 'new_cuts': found, 'shared_cuts': len(known), 'variables': enc.nv,
           'clauses': len(enc.clauses), 'share_clauses': enc.n_share - enc.n_base,
           'counter_clauses': len(enc.clauses) - enc.n_share - len(known) - len(found)}
    if not check:
        rec['sec'] = round(tsolve, 2)
        return rec
    if found:   # cold proof on the final clause set (see certify_direction.one)
        with S(bootstrap_with=enc.clauses, with_proof=True) as s:
            assert not s.solve()
            proof = s.get_proof()
    tsolve = time.time() - t0
    os.makedirs(TMP, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=TMP) as td:
        cnf, prf = os.path.join(td, 'f.cnf'), os.path.join(td, 'f.drup')
        write_cnf(enc, cnf)
        with open(prf, 'w') as f:
            f.write('\n'.join(proof) + '\n')
        nlines = len(proof); del proof
        pbytes = os.path.getsize(prf)
        t1 = time.time()
        r = subprocess.run([ensure_drat(), cnf, prf, '-t', '20000'], capture_output=True, text=True)
        tcheck = time.time() - t1
        if keep:
            import gzip, shutil
            os.makedirs(keep, exist_ok=True)
            tag = 'd' + ''.join(map(str, dirs)) + '_a' + '_'.join(f'{a[0]}' if a[0] == a[1] else f'{a[0]}-{a[1]}' for a in alpha) + f'_B{B}'
            for f in (cnf, prf):
                with open(f, 'rb') as fi, gzip.open(os.path.join(keep, tag + os.path.splitext(f)[1] + '.gz'), 'wb') as fo:
                    shutil.copyfileobj(fi, fo)
    rec.update({'verified': 's VERIFIED' in r.stdout, 'proof_lines': nlines, 'proof_bytes': pbytes,
                'solve_sec': round(tsolve, 2), 'check_sec': round(tcheck, 2), 'sec': round(time.time() - t0, 2)})
    return rec


def _child(conn, args, mem):
    os.setpgid(0, 0)
    if mem:
        resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
    try:
        if args[6] == 'bin':
            conn.send(_attempt_bin(*args[:6], *args[7:]))
        else:
            conn.send(_attempt(*args))
    except MemoryError:
        conn.send({'status': 'MEMOUT'})
    conn.close()


def attempt(dirs, alpha, B, radius=3, counter='stot', exact=True, solver='bin', check=True,
            tl=None, mem=1900 * 2**20, keep=None):
    """Run one attempt in a child process; returns a record, status UNKNOWN on timeout."""
    ctx = mp.get_context('fork')
    a, b = ctx.Pipe(False)
    p = ctx.Process(target=_child, args=(b, (dirs, alpha, B, radius, counter, exact, solver, check, keep), mem))
    t0 = time.time()
    p.start(); b.close()
    rec = None
    if a.poll(tl):
        try:
            rec = a.recv()
        except EOFError:
            rec = None
    if rec is None:
        try:
            os.killpg(p.pid, 9)
        except ProcessLookupError:
            pass
        p.join()
        # kill any drat-trim the child left behind
        rec = {'status': 'UNKNOWN' if tl and time.time() - t0 >= tl else 'CRASH'}
    p.join()
    import glob, shutil
    for d in glob.glob(os.path.join(TMP, f'a{p.pid}_*')):
        shutil.rmtree(d, ignore_errors=True)
    rec['wall'] = round(time.time() - t0, 2)
    save_cuts(dirs, radius, rec.pop('new_cuts', []))
    rec['B'] = B
    return rec


def search(dirs, alpha, lo=0, hi=None, tl=120, verbose=True, **kw):
    """Largest LB with 'sum <= LB-1' certified UNSAT within tl seconds per attempt.
    lo: an LB already known (0 is trivial).  hi: an upper limit for LB (default from a SAT probe)."""
    log = []
    best = lo                              # certified LB (sum >= best)
    if hi is None:
        r = attempt(dirs, alpha, None, check=False, tl=tl, **kw)
        log.append(r)
        if r['status'] != 'SAT':
            return {'LB': None, 'log': log}
        hi = r['sum']                      # a real configuration: LB <= hi
    # invariant: LB in [best, hi]; try B = mid-1 meaning LB = mid
    while best < hi:
        mid = (best + hi + 1) // 2
        r = attempt(dirs, alpha, mid - 1, tl=tl, **kw)
        log.append(r)
        if verbose:
            print(' B', mid - 1, r['status'], r.get('verified'), r.get('sec'), r.get('wall'), flush=True)
        if r['status'] == 'UNSAT' and r.get('verified'):
            best = mid
        elif r['status'] == 'SAT':
            hi = min(mid - 1, r['sum'])
        else:
            hi = mid - 1                   # not certifiable within tl
    return {'LB': best, 'log': log}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dirs', type=int, nargs='+', required=True)
    ap.add_argument('--alpha', nargs='+', required=True, help='k or lo-hi per centre')
    ap.add_argument('--B', type=int)
    ap.add_argument('--search', action='store_true')
    ap.add_argument('--tl', type=float, default=300)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--counter', default='stot', choices=['swc', 'tot', 'stot'])
    ap.add_argument('--solver', default='bin', choices=list(SOLVERS) + ['bin'])
    ap.add_argument('--keep')
    a = ap.parse_args()
    alpha = [tuple(map(int, x.split('-'))) if '-' in x else (int(x), int(x)) for x in a.alpha]
    kw = dict(radius=a.radius, counter=a.counter, solver=a.solver)
    if a.search:
        r = search(a.dirs, alpha, tl=a.tl, **kw)
        print(json.dumps({'dirs': a.dirs, 'alpha': alpha, 'LB': r['LB'],
                          'log': [{k: v for k, v in x.items() if k != 'sel'} for x in r['log']]}))
    else:
        r = attempt(a.dirs, alpha, a.B, tl=a.tl, keep=a.keep, **kw)
        r.pop('sel', None)
        print(json.dumps(r))


if __name__ == '__main__':
    main()
