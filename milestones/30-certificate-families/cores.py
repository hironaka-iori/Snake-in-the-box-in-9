"""UNSAT cores of the 9,784 new k7 keys, mapped to the clause families of wincert.Encoding.

For each paid key of keys_best234: the radius-4 CNF of k7.encoding (plus lazy cycle cuts when
CaDiCaL finds a cyclic model), CaDiCaL --unsat --lrat streamed through a FIFO into lrattrim
(the proof never touches the disk), and the original clauses of the empty clause's cone.
Recorded per key (data/cores.jsonl):
  hints, lemmas, core       trimmed proof of the full CNF (one run, --seed=1 --unsat)
  win                       window positions whose unit clause 'window' is in the core
  lo, hi                    centre positions (1-based) whose alpha>=lo / alpha<=hi counter
                            clauses are in the core
  cuts, cuts_used           cycle cuts added / in the core
  sup                       hex bitmask (512 bits) of the cube vertices whose selection
                            variable occurs in a core clause
Only the CNF of the current key is on disk (a few MB, deleted at once).

  nice -n 15 python cores.py [--limit N] [--order cheap|dear]
"""
import sys, os, json, gzip, time, subprocess, argparse
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
M25 = os.path.join(HERE, '..', '25-k7-234')
sys.path.insert(0, M25)
import k7  # noqa: E402

SCR = os.environ.get('FAM_SCR', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/'
                     '9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/families')
TRIM = os.path.join(SCR, 'bin', 'lrattrim')
CAD = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
OUT = os.path.join(HERE, 'data', 'cores.jsonl')


def disk_mb():
    st = os.statvfs('/')
    return st.f_bavail * st.f_frsize / 2 ** 20


def write(clauses, nv, path):
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n')
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')


def lrat_core(cnf, ncl, wd, args=('--seed=1', '--unsat'), tl=600):
    """(status, lemmas, hints, core ids) of one CaDiCaL run, proof streamed through a FIFO."""
    fifo = os.path.join(wd, 'p.fifo'); cids = os.path.join(wd, 'core.ids')
    for f in (fifo, cids):
        if os.path.exists(f):
            os.remove(f)
    os.mkfifo(fifo)
    tr = subprocess.Popen([TRIM, str(ncl), fifo, cids], stdout=subprocess.PIPE, text=True)
    cad = subprocess.run([CAD, '-q', '--lrat', '--no-binary', *args, cnf, fifo],
                         capture_output=True, text=True, timeout=tl)
    out, _ = tr.communicate(timeout=tl)
    os.remove(fifo)
    if cad.returncode == 10:
        if os.path.exists(cids):
            os.remove(cids)
        return 'SAT', cad.stdout, None, None
    if cad.returncode != 20 or tr.returncode != 0:
        raise RuntimeError(f'cadical rc {cad.returncode}, trim rc {tr.returncode}')
    lem, hints, nc = (int(x) for x in out.split())
    ids = [int(x) for x in open(cids)]
    os.remove(cids)
    return 'UNSAT', lem, hints, ids


def model_sel(enc, stdout):
    pos = set()
    for l in stdout.splitlines():
        if l.startswith('v'):
            pos |= {int(x) for x in l[1:].split() if int(x) > 0}
    return [v for v in enc.ball if enc.var[v] in pos]


def one(k, wd):
    enc = k7.encoding(k)
    t = time.time()
    cnf = os.path.join(wd, 'f.cnf')
    cuts = 0
    try:
        while True:
            write(enc.clauses, enc.nv, cnf)
            st, lem, hints, ids = lrat_core(cnf, len(enc.clauses), wd)
            if st == 'UNSAT':
                break
            # cyclic model: add every cut the incremental lazy-cut solve needs (wincert.decide
            # adds them to enc), then one more proof run
            n0 = len(enc.clauses)
            st2, _, _ = k7.W.decide(enc, certify=False)
            if st2 != 'UNSAT':
                return dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result=st2)
            cuts += len(enc.clauses) - n0
    finally:
        if os.path.exists(cnf):
            os.remove(cnf)
    W = enc.window
    win, lo, hi, cu = set(), set(), set(), 0
    sup = 0
    nb = len(enc.ball)
    for i in ids:
        kind = enc.kinds[i - 1]
        if kind == 'window':
            win.add(W.index(enc.ball[enc.clauses[i - 1][0] - 1]))
        elif kind.startswith('alpha'):
            c = int(kind.split('@')[1]); p = W.index(c)
            (lo if kind.startswith('alpha>=') else hi).add(p)
        elif kind == 'cycle_cut':
            cu += 1
        for l in enc.clauses[i - 1]:
            v = abs(l)
            if v <= nb:
                sup |= 1 << enc.ball[v - 1]
    return dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result='UNSAT', hints=hints, lemmas=lem,
                core=len(ids), ncl=len(enc.clauses), win=sorted(win), lo=sorted(lo), hi=sorted(hi),
                cuts=cuts, cuts_used=cu, sup=format(sup, 'x'), s=round(time.time() - t, 3))


def records():
    """The records of data/cores.jsonl, or of the committed data/cores.jsonl.gz."""
    if os.path.exists(OUT):
        return [json.loads(l) for l in open(OUT)]
    return [json.loads(l) for l in gzip.open(OUT + '.gz', 'rt')]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--order', default='cheap')
    a = ap.parse_args()
    d = json.load(gzip.open(os.path.join(M25, 'data', 'keys_best234.json.gz'), 'rt'))
    todo = [(h, (k[0], tuple(k[1]), tuple(k[2]))) for k, b, h in zip(d['keys'], d['basis'], d['hints'])
            if b != 'reuse']
    todo.sort(reverse=(a.order == 'dear'))
    done = set()
    if os.path.exists(OUT) or os.path.exists(OUT + '.gz'):
        for r in records():
            done.add((r['kind'], tuple(r['dirs']), tuple(r['syms'])))
    wd = os.path.join(SCR, 'work'); os.makedirs(wd, exist_ok=True)
    n = 0; t0 = time.time()
    with open(OUT, 'a') as f:
        for h, k in todo:
            if k in done:
                continue
            if disk_mb() < 300:
                print('disk low, stop', flush=True); break
            try:
                r = one(k, wd)
            except Exception as e:      # noqa: BLE001
                r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result='ERROR', err=str(e)[:200])
            r['model_hints'] = h
            f.write(json.dumps(r, separators=(',', ':')) + '\n'); f.flush()
            n += 1
            if n % 200 == 0:
                print(n, round(time.time() - t0), k7.rss_mb(), flush=True)
            if a.limit and n >= a.limit:
                break
    print('done', n, round(time.time() - t0))


if __name__ == '__main__':
    main()
