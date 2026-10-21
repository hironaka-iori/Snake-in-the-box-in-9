"""Symmetry-broken certificates for the 55 most expensive direction windows of the 239 bound.

CNF = the committed window CNF (wincert encoding + cycle cuts, sha256-checked) + lex-leader
clauses for the adjacent transpositions of the free coordinates (auxiliary variables after all
base variables).  Solved with CaDiCaL 1.9.5 through PySAT (deterministic), the DRUP proof trimmed
to LRAT by drat-trim -L.  The LRAT is untrusted: the Lean kernel replays every step, and
`D239LexG1` proves that a snake satisfies the lex clauses after a cube normalisation.

usage: python3 -I symsolve.py WORK TAG...   reads WORK/data/TAG.cnf, writes WORK/sym/TAG.{cnf,lrat,json}
"""
import sys, time, subprocess, json, os

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'milestones', '10-window-aggregate', 'scripts'))
DT = os.environ.get('DRAT_TRIM', os.path.join(REPO, 'milestones', '10-window-aggregate', '.build', 'drat-trim'))


def swapN(a, b, v):
    return v if (v >> a & 1) == (v >> b & 1) else v ^ (1 << a | 1 << b)


def lexgens(dirs):
    used = set(dirs)
    free = [k for k in range(9) if k not in used]
    return [(free[i], free[i + 1]) for i in range(len(free) - 1)]


def lex_clauses(enc, gens, vb):
    X = enc.var
    out, info, nv = [], [], vb - 1
    for a, b in gens:
        pairs = [(v, swapN(a, b, v)) for v in enc.ball if swapN(a, b, v) != v]
        base = nv + 1
        e = None
        for i, (v, w) in enumerate(pairs):
            x, y = X[v], X[w]
            cond = [] if e is None else [-e]
            out.append(cond + [-x, y])
            if i + 1 < len(pairs):
                nv += 1
                out.append(cond + [-x, -y, nv]); out.append(cond + [x, y, nv])
                e = nv
        assert nv == base + len(pairs) - 2
        info.append((a, b, base, len(pairs)))
    return out, info, nv


def run(tag, work, case):
    from wincert import Encoding, window_from_dirs
    from pysat.solvers import Solver
    al = [lo if lo == hi else (lo, hi) for lo, hi in case['alpha']]
    enc = Encoding(window_from_dirs(case['dirs']), al, 3)
    raw = open(f'{work}/data/{tag}.cnf').read().splitlines()
    clauses = [list(map(int, l.split()))[:-1] for l in raw if l and l[0] not in 'pc']
    assert clauses[:len(enc.clauses)] == enc.clauses
    assert max(abs(l) for cl in clauses for l in cl) <= enc.nv
    vb = enc.nv + 1
    extra, info, nv = lex_clauses(enc, lexgens(case['dirs']), vb)
    allc = clauses + extra
    os.makedirs(f'{work}/sym', exist_ok=True)
    t = time.time()
    with Solver(name='cadical195', bootstrap_with=allc, with_proof=True) as s:
        assert not s.solve()
        pr = s.get_proof()
    ts = time.time() - t
    cnf = f'{work}/sym/{tag}.cnf'
    with open(cnf, 'w') as o:
        o.write(f'p cnf {nv} {len(allc)}\n')
        for cl in allc: o.write(' '.join(map(str, cl)) + ' 0\n')
    with open(cnf + '.drup', 'w') as o:
        for l in pr: o.write(l + '\n')
    del pr
    t = time.time()
    rr = subprocess.run(['nice', '-n', '10', DT, cnf, cnf + '.drup', '-L', f'{work}/sym/{tag}.lrat', '-t', '20000'],
                        stdin=subprocess.DEVNULL, capture_output=True, text=True)
    tt = time.time() - t
    os.remove(cnf + '.drup')
    ok = 's VERIFIED' in rr.stdout
    assert ok, tag
    st = h = 0
    for line in open(f'{work}/sym/{tag}.lrat'):
        x = line.split()
        if x[1] == 'd': continue
        z = x.index('0', 1); st += 1; h += len(x) - z - 2
    res = dict(tag=tag, vb=vb, nbase=len(clauses), nlex=len(extra), gens=info, solve=round(ts, 1),
               trim=round(tt, 1), verified=ok, steps=st, hints=h)
    json.dump(res, open(f'{work}/sym/{tag}.json', 'w'))
    print(json.dumps(res), flush=True)
    return res


if __name__ == '__main__':
    cases = {c['tag']: c for c in json.load(open(os.path.join(HERE, 'cases.json')))}
    for t in sys.argv[2:]:
        run(t, sys.argv[1], cases[t])
