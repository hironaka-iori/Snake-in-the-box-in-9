"""Cold solves of a share CNF with the CaDiCaL binary and lazy cycle cuts (track A, milestone 38).
solve(enc, opts, tl) -> (status, seconds, cuts, conflicts); the cuts stay in enc.clauses."""
import os, re, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '28-combined-identities'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 's0_share_loop'))
from wincert import cycles_of
CADICAL = os.environ.get('CADICAL', '/usr/local/bin/cadical')


def write_cnf(clauses, nv, path):
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(clauses)}\n')
        f.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses))


def solve(enc, opts=(), tl=900, extra=()):
    t0 = time.time(); cuts = 0; confl = 0
    extra = [list(c) for c in extra]
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, 'x.cnf')
        while True:
            left = tl - (time.time() - t0)
            if left <= 1:
                return 'TIMEOUT', time.time() - t0, cuts, confl
            cl = [list(c) for c in enc.clauses] + extra
            nv = max(enc.nv, max((abs(l) for c in extra for l in c), default=0))
            write_cnf(cl, nv, p)
            r = subprocess.run([CADICAL, '-t', str(int(left))] + list(opts) + [p], capture_output=True, text=True)
            m = re.search(r'c conflicts:\s+(\d+)', r.stdout)
            confl += int(m.group(1)) if m else 0
            if r.returncode == 20:
                return 'UNSAT', time.time() - t0, cuts, confl
            if r.returncode != 10:
                return 'TIMEOUT', time.time() - t0, cuts, confl
            pos = {int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x) > 0}
            sel = [v for v in enc.ball if enc.var[v] in pos]
            cyc = cycles_of(sel)
            if not cyc:
                return 'SAT', time.time() - t0, cuts, confl
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
