"""How many "long windows" (7-8 counted centres, 8-9 directions) would the k6 automaton need?

The k6 product (34 shapes x 6^5 lumped counts; `cutloop.base_graph`) remembers 7 directions and
5 counts.  A walk of k transitions from a state spells a window of 7 + k directions with 5 + k
counted centres (the first centre of the 7-shape carries no count).  A long-window exclusion is
such a window that is UNSAT in the radius-4 local model (wincert.Encoding, exact lumped counts,
cycle cuts), although each of its 6-centre sub-windows is allowed by the automaton.

For lam = minimum cycle mean, pi an optimal integer potential and rc = Q s - P + pi(u) - pi(v),
a cycle has mean lam + mean(rc)/Q.  Raising the bound to lam' needs every cycle of the
subgraph G_r = {rc <= r} with mean < lam' broken; G_0 is the critical subgraph.

This script
  * counts k-walks (k = 1, 2, 3) in G_0 and G_r (r = 1, 2): the number of candidate windows;
  * samples random k-walks in G_0, builds one concrete labelling (a fresh step takes, at
    random, the direction 7 back or a new label), and decides them at radius 4;
  * certifies a few UNSAT samples (CaDiCaL DRUP -> drat-trim -L LRAT) for the proof size.

  nice -n 19 python longwin.py allknown|keys235 [samples] [certify]
"""
import sys, os, json, time, random, subprocess, tempfile
from fractions import Fraction as Fr
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import cutloop as CL  # noqa: E402  (puts 10-window-aggregate/scripts on the path)
import wincert as W  # noqa: E402
from shapes import canon  # noqa: E402

NC = CL.NC
LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)


def kwalks(n, U, V, k):
    x = np.ones(n)
    out = []
    for _ in range(k):
        x = np.bincount(V, weights=x[U], minlength=n)
        out.append(float(x.sum()))
    return out


def decode_counts(c):
    """5 lumped symbols of a count index, oldest first (newest = least significant digit)."""
    return [(c // 6 ** k) % 6 + 1 for k in range(4, -1, -1)]


def window(shp, walk, U, V, S, rnd):
    """Concrete directions and per-centre alpha list of a walk (list of edge ids)."""
    a = int(U[walk[0]]) // NC
    seq = list(shp[a])
    al = [None] + [LUMP[s] for s in decode_counts(int(U[walk[0]]) % NC)]   # centres w1..w6
    for e in walk:
        b = int(V[e]) // NC
        tail = seq[-6:]
        opts = [d for d in range(9) if canon(tail + [d]) == tuple(shp[b])]
        rep = [d for d in opts if d in tail]
        d = rep[0] if rep else rnd.choice(opts)    # fresh: any coordinate not among the last 6
        seq.append(d)
        al.append(LUMP[int(S[e])])
    return seq, al


def decide(seq, al, radius=4):
    vs = [0]
    for d in seq:
        vs.append(vs[-1] ^ 1 << d)
    enc = W.Encoding(vs, al, radius)
    st, _, cuts = W.decide(enc, certify=False)
    return st, enc


def lrat_size(enc):
    from pysat.solvers import Cadical153
    with tempfile.TemporaryDirectory(dir=os.environ.get('SCRATCH')) as td:
        cnf, prf, lr = (os.path.join(td, f) for f in ('f.cnf', 'f.drup', 'f.lrat'))
        W.write_cnf(enc, cnf)
        with Cadical153(bootstrap_with=enc.clauses, with_proof=True) as s:
            assert not s.solve()
            proof = s.get_proof()
        open(prf, 'w').write('\n'.join(proof) + '\n')
        r = subprocess.run([W.ensure_drat(), cnf, prf, '-L', lr, '-t', '600'], capture_output=True, text=True)
        ok = 's VERIFIED' in r.stdout
        size = os.path.getsize(lr) if os.path.exists(lr) else None
        lines = sum(1 for _ in open(lr)) if size else None
        return dict(verified=ok, drup_lines=len(proof), lrat_bytes=size, lrat_lines=lines,
                    clauses=len(enc.clauses), variables=enc.nv)


def main():
    which = sys.argv[1]
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    ncert = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    t0 = time.time()
    shp, u, v, s, nkeys = CL.base_graph(which)
    n = len(shp) * NC
    m = CL.prune(n, u, v); u, v, s = u[m], v[m], s[m]
    bf = CL.BF(n, u, v, s)
    lam, cyc, pi, it = CL.mcm(bf, Fr(4))
    P, Q = lam.numerator, lam.denominator
    rc = Q * s - P + pi[u] - pi[v]
    live = np.zeros(n, bool); live[u] = True
    print(f'{which}: lam {lam}, {len(u)} live transitions, potential range {int(pi[live].max() - pi[live].min())}, '
          f'{time.time() - t0:.0f}s, rss {CL.rss_mb():.0f} MB', flush=True)
    res = dict(which=which, nkeys=nkeys, lam=str(lam), transitions=int(len(u)),
               pot_range=int(pi[live].max() - pi[live].min()), graphs={})
    for r in (0, 1, 2, 4):
        mm = rc <= r
        mk = CL.prune(n, u[mm], v[mm])
        U, V = u[mm][mk], v[mm][mk]
        res['graphs'][f'rc<={r}'] = dict(transitions=int(len(U)), max_mean_gain=str(Fr(r, Q)),
                                         walks_k1_k2_k3=kwalks(n, U, V, 3))
        print(r, res['graphs'][f'rc<={r}'], flush=True)
    # samples in G0 (pruned to its cyclic part)
    z = rc == 0
    mk = CL.prune(n, u[z], v[z])
    U, V, S = u[z][mk], v[z][mk], s[z][mk]
    order = np.argsort(U, kind='stable')
    U, V, S = U[order], V[order], S[order]
    first = np.searchsorted(U, np.arange(n)); last = np.searchsorted(U, np.arange(n), side='right')
    rnd = random.Random(1)
    out = {}
    certs = []
    for k in (1, 2, 3):
        stats = dict(SAT=0, UNSAT=0, UNKNOWN=0)
        ex = []
        for _ in range(nsamp):
            e = rnd.randrange(len(U)); walk = [e]
            while len(walk) < k:
                x = int(V[walk[-1]])
                walk.append(rnd.randrange(first[x], last[x]))
            seq, al = window(shp, walk, U, V, S, rnd)
            st, enc = decide(seq, al)
            stats[st] += 1
            if st == 'UNSAT':
                if len(ex) < 5:
                    ex.append(dict(dirs=seq, alpha=[a[0] if a else None for a in al]))
                if k >= 2 and len(certs) < ncert * (k - 1):
                    certs.append(dict(k=k, centres=len(al) - 1, **lrat_size(enc)))
                    print('cert', certs[-1], flush=True)
        out[f'k{k}'] = dict(centres=5 + k, directions=7 + k, samples=nsamp, **stats, unsat_examples=ex)
        print(k, {a: b for a, b in out[f'k{k}'].items() if a != 'unsat_examples'}, f'{time.time() - t0:.0f}s', flush=True)
    res['G0_samples'] = out
    res['certificates'] = certs
    res['seconds'] = round(time.time() - t0)
    json.dump(res, open(os.path.join(HERE, 'data', f'longwin_{which}.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
