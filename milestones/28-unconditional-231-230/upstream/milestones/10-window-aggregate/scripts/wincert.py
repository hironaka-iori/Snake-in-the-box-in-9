"""CNF encoding of a local path-window problem with DRUP certification.

A window is a list of consecutive path vertices x_0..x_{k+1}; the k centers
x_1..x_k are internal path vertices with prescribed singleton-square counts.
Every clause is a necessary condition on S cap B for a snake S in Q9, where
B is the radius-r Hamming ball around the centers.
"""
import itertools, os, subprocess, tempfile
from itertools import combinations
from pysat.solvers import Cadical153

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
DRAT_SOURCE = os.path.join(ROOT, 'work', 'keep96', 'vendor', 'drat-trim', 'drat-trim.c')
DRAT_SOURCE_SHA256 = 'd834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee'
DRAT = os.path.join(HERE, '..', '.build', 'drat-trim')


def ensure_drat():
    """Compile the vendored drat-trim source (hash-checked) if needed."""
    import hashlib
    if os.path.exists(DRAT):
        return DRAT
    digest = hashlib.sha256(open(DRAT_SOURCE, 'rb').read()).hexdigest()
    assert digest == DRAT_SOURCE_SHA256, digest
    os.makedirs(os.path.dirname(DRAT), exist_ok=True)
    subprocess.run(['gcc', '-O2', '-std=c99', '-Dgetc_unlocked=getc', DRAT_SOURCE, '-o', DRAT], check=True)
    return DRAT


def window_from_dirs(ds):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ 1 << d)
    return vs


def cycles_of(sel):
    sel = set(sel)
    adj = {v: [w for w in sel if (v ^ w).bit_count() == 1] for v in sel}
    seen, out = set(), []
    for s in sorted(sel):
        if s in seen:
            continue
        st, comp = [s], []
        while st:
            v = st.pop()
            if v in seen:
                continue
            seen.add(v); comp.append(v); st.extend(adj[v])
        if len(comp) > 2 and all(len(adj[v]) == 2 for v in comp):
            out.append(sorted(comp))
    return out


class Encoding:
    def __init__(self, window, alpha, radius, ends=2, empties=None):
        self.window, self.alpha, self.radius, self.ends = list(window), list(alpha), radius, ends
        # empties[i]: None, k, or (lo, hi) for e(x_{i+1}) = number of empty squares Q with
        # x_{i+1} adjacent to a vertex of Q (252 squares, all inside the radius-3 ball).
        self.empties = list(empties) if empties is not None else [None] * len(self.alpha)
        self.esq = {}
        centers = window[1:-1]
        self.ball = [v for v in range(512) if min((v ^ c).bit_count() for c in centers) <= radius]
        self.B = set(self.ball)
        self.var = {v: i + 1 for i, v in enumerate(self.ball)}
        self.nv = len(self.ball)
        self.clauses, self.kinds = [], []
        self.build()

    def fresh(self):
        self.nv += 1
        return self.nv

    def add(self, c, kind):
        self.clauses.append(list(c)); self.kinds.append(kind)

    def build(self):
        X, B = self.var, self.B
        for v in self.window:
            self.add([X[v]], 'window')
        endvars = []
        for v in self.ball:
            ns = [X[v ^ 1 << k] for k in range(9) if v ^ 1 << k in B]
            for a, b, c in combinations(ns, 3):
                self.add([-X[v], -a, -b, -c], 'degree<=2')
            if len(ns) == 9:
                e = self.fresh(); endvars.append(e)
                self.add([-X[v]] + ns, 'interior_degree>=1')
                self.add([-e, X[v]], 'end_selected')
                for w in ns:
                    self.add([-X[v], e] + [t for t in ns if t != w], 'degree1->end')
                for a, b in combinations(ns, 2):
                    self.add([-e, -a, -b], 'end->degree<=1')
        self.atmost(endvars, self.ends, 'endpoint_budget')
        centers = self.window[1:-1]
        for i, c in enumerate(centers, 1):
            used = {(c ^ self.window[i - 1]).bit_length() - 1, (c ^ self.window[i + 1]).bit_length() - 1}
            corners = [X[c ^ 1 << a ^ 1 << b] for a, b in combinations(range(9), 2)
                       if a not in used and b not in used]
            assert len(corners) == 21
            k = self.alpha[i - 1]
            if k is None:
                continue
            if isinstance(k, tuple):
                lo, hi = k
            else:
                lo = hi = k
            absent = [-c2 for c2 in corners]
            if hi < 21:
                self.atmost(absent, hi, f'alpha<={hi}@{c}')
            if lo > 0:
                self.atmost(corners, 21 - lo, f'alpha>={lo}@{c}')
        for i, c in enumerate(centers, 1):
            k = self.empties[i - 1]
            if k is None:
                continue
            lo, hi = k if isinstance(k, tuple) else (k, k)
            evars = []
            for y in (c ^ 1 << d for d in range(9)):
                for a, b in combinations(range(9), 2):
                    sq = sorted({y, y ^ 1 << a, y ^ 1 << b, y ^ 1 << a ^ 1 << b})
                    if c in sq:
                        continue
                    assert all(w in B for w in sq), (c, sq)
                    key = tuple(sq)
                    if key not in self.esq:
                        e = self.fresh(); self.esq[key] = e
                        for w in sq:
                            self.add([-e, -X[w]], 'empty->unselected')
                        self.add([e] + [X[w] for w in sq], 'selected_or_empty')
                    evars.append(self.esq[key])
            assert len(evars) == 252, len(evars)
            if hi < 252:
                self.atmost(evars, hi, f'e<={hi}@{c}')
            if lo > 0:
                self.atmost([-e for e in evars], 252 - lo, f'e>={lo}@{c}')
        for v in self.ball:
            for a, b in combinations(range(9), 2):
                if v >> a & 1 or v >> b & 1:
                    continue
                sq = [v, v | 1 << a, v | 1 << b, v | 1 << a | 1 << b]
                if all(w in B for w in sq):
                    self.add([-X[w] for w in sq], 'no4cycle')
            for t in combinations(range(9), 3):
                if any(v >> k & 1 for k in t):
                    continue
                cube = [v ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
                if all(w in B for w in cube):
                    for r in range(4):
                        self.add([-X[cube[s]] for s in range(8) if s not in (r, 7 - r)], 'no6cycle')

    def atmost(self, lits, k, kind):
        """Sequential counter (Sinz): at most k of lits are true."""
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self.add([-l], kind)
            return
        s = [[self.fresh() for _ in range(k)] for _ in range(n)]
        self.add([-lits[0], s[0][0]], kind)
        for j in range(1, k):
            self.add([-s[0][j]], kind)
        for i in range(1, n):
            self.add([-lits[i], s[i][0]], kind)
            self.add([-s[i - 1][0], s[i][0]], kind)
            for j in range(1, k):
                self.add([-lits[i], -s[i - 1][j - 1], s[i][j]], kind)
                self.add([-s[i - 1][j], s[i][j]], kind)
            self.add([-lits[i], -s[i - 1][k - 1]], kind)

    def add_cycle_cut(self, cyc):
        assert all(sum((a ^ b).bit_count() == 1 for b in cyc) == 2 for a in cyc)
        self.add([-self.var[w] for w in cyc], 'cycle_cut')


def decide(enc, max_rounds=10000, certify=True):
    """Return ('SAT', selection, cuts) or ('UNSAT', proof-check info, cuts).

    Cycle cuts are added incrementally to one solver instance; the proof run
    (when certifying) is a separate cold solve of the final clause set."""
    cuts = 0
    with Cadical153(bootstrap_with=enc.clauses) as s:
        while True:
            if not s.solve():
                break
            model = s.get_model()
            sel = [v for v in enc.ball if model[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc:
                return 'SAT', sel, cuts
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
                s.add_clause(enc.clauses[-1])
            if cuts > max_rounds:
                return 'UNKNOWN', None, cuts
    if not certify:
        return 'UNSAT', None, cuts
    return 'UNSAT', certify_unsat(enc), cuts


def write_cnf(enc, path):
    with open(path, 'w') as f:
        f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
        for c in enc.clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')


def certify_unsat(enc):
    with tempfile.TemporaryDirectory() as td:
        cnf = os.path.join(td, 'f.cnf'); prf = os.path.join(td, 'f.drup')
        write_cnf(enc, cnf)
        with Cadical153(bootstrap_with=enc.clauses, with_proof=True) as s:
            assert not s.solve()
            proof = s.get_proof()
        with open(prf, 'w') as f:
            f.write('\n'.join(proof) + '\n')
        r = subprocess.run([ensure_drat(), cnf, prf, '-t', '600'], capture_output=True, text=True)
        ok = 's VERIFIED' in r.stdout
        return {'verified': ok, 'proof_lines': len(proof), 'clauses': len(enc.clauses),
                'variables': enc.nv, 'drat_tail': r.stdout.strip().splitlines()[-1:]}
