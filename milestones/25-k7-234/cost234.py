"""Measured replay cost of k7 keys (milestone 25, cut of the 234 certificate cost).

replay_cost(key) follows the certify pipeline of the 235 build (gen_lean_core.full_core_ids +
core_lrat): lazy-cut solve -> committed CNF; core = original clauses of the trimmed proof of
the full CNF (configurations --unsat and default, the fewer hints wins); then the CaDiCaL
portfolio on the core alone (PORTFOLIO x seeds 1,2), trimmed, fewest hints wins.  The proofs
are never written to disk: CaDiCaL writes into a FIFO read by lrattrim (C, in memory).  Only the
CNF (a few MB) touches the scratch directory, and it is deleted at once.
"""
import sys, os, json, time, subprocess, tempfile
sys.dont_write_bytecode = True
import k7

SCR = os.environ.get('SCR234', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/'
                     '9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/cost234')
TRIM = os.path.join(SCR, 'bin', 'lrattrim')
CAD = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
PORTFOLIO = [[], ['--unsat'], ['--chrono=0'], ['--unsat', '--probe=0'], ['--unsat', '--shrink=0'],
             ['--unsat', '--chrono=0'], ['--unsat', '--subsume=0']]
FULL = [['--unsat'], []]


def disk_mb():
    st = os.statvfs('/')
    return st.f_bavail * st.f_frsize / 2 ** 20


def runs(portfolio, seeds=(1, 2)):
    out = []
    for ex in portfolio:
        for s in (seeds[:1] if '--unsat' in ex else seeds):
            out.append([f'--seed={s}', *ex])
    return out


def lrat(cnf, ncl, args, wd, core_out=None, tl=900):
    """(lemmas, hints, core size) of a trimmed CaDiCaL proof, the proof streamed through a FIFO."""
    fifo = os.path.join(wd, 'p.fifo')
    if os.path.exists(fifo):
        os.remove(fifo)
    os.mkfifo(fifo)
    tr = subprocess.Popen([TRIM, str(ncl), fifo] + ([core_out] if core_out else []),
                          stdout=subprocess.PIPE, text=True)
    cad = subprocess.run([CAD, '-q', '--lrat', '--no-binary', *args, cnf, fifo],
                         capture_output=True, text=True, timeout=tl)
    out, _ = tr.communicate(timeout=tl)
    os.remove(fifo)
    if cad.returncode != 20 or tr.returncode != 0:
        raise RuntimeError(f'cadical rc {cad.returncode}, trim rc {tr.returncode}: {cad.stdout[-200:]}')
    return tuple(int(x) for x in out.split())


def write(clauses, nv, path):
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n')
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')


def replay_cost(k, portfolio=PORTFOLIO, seeds=(1, 2), wd=None):
    """k = (kind, dirs, syms) with kind 'k6' or 'H'.  Returns a record (hints = the replay's)."""
    assert disk_mb() > 420, 'disk low'
    wd = wd or tempfile.mkdtemp(dir=SCR)
    enc = k7.encoding(k)
    t = time.time()
    st, _, cuts = k7.W.decide(enc, certify=False)
    r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result=st, solve_s=round(time.time() - t, 3),
             cuts=cuts, nv=enc.nv, ncl=len(enc.clauses))
    if st != 'UNSAT':
        return r
    cnf = os.path.join(wd, 'f.cnf'); ccnf = os.path.join(wd, 'c.cnf'); cids = os.path.join(wd, 'core.ids')
    try:
        write(enc.clauses, enc.nv, cnf)
        best = None
        t = time.time()
        for a in runs(FULL, seeds[:1]):
            l, h, c = lrat(cnf, len(enc.clauses), a, wd, cids + '.tmp')
            r.setdefault('full', []).append([' '.join(a), h])
            if best is None or h < best[0]:
                best = (h, l, c); os.replace(cids + '.tmp', cids)
        r['full_s'] = round(time.time() - t, 2)
        r['full_hints'], r['core'] = best[0], best[2]
        ids = [int(x) for x in open(cids)]
        write([enc.clauses[i - 1] for i in ids], enc.nv, ccnf)
        t = time.time()
        bh = None
        for a in runs(portfolio, seeds):
            l, h, c = lrat(ccnf, len(ids), a, wd)
            if bh is None or h < bh[0]:
                bh = (h, l, c, ' '.join(a))
        r['core_s'] = round(time.time() - t, 2)
        r['hints'], r['lemmas'], r['core_used'], r['config'] = bh
    finally:
        for f in (cnf, ccnf, cids, cids + '.tmp'):
            if os.path.exists(f):
                os.remove(f)
    return r


if __name__ == '__main__':
    k = (sys.argv[1], tuple(json.loads(sys.argv[2])), tuple(json.loads(sys.argv[3])))
    print(json.dumps(replay_cost(k)))
