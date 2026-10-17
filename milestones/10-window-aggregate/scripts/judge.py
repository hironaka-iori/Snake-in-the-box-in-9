"""Independent end-to-end judge for the conditional bounds 242 and 241.

This program does not trust wincert.py, certify.py or aggregate.py.  It decides
four questions and prints a verdict for each.

  A. Re-encoding.  Every premise is re-encoded from the definitions by code
     written separately here (different variable order, different cardinality
     encoding).  The cycle cuts recorded with the stored certificate are first
     checked to be genuine cycles of Q9.  Glucose 4 refutes each formula and
     emits a DRUP proof, which drat-trim checks.
  B. Clause audit.  Every stored-certificate clause over vertex variables only
     is classified semantically: window unit, three neighbours of a selected
     vertex, a 4-cycle, an induced 6-cycle of a 3-face, or a recorded cycle.
     An unclassifiable clause is a failure.
  C. Bridge test.  Every window of every available snake, whose canonical shape
     is one of the certified shapes, is normalised by translation and
     coordinate relabelling.  Its true restriction must satisfy the judge's own
     encoding with its true counts.  This tests normalisation and encoding
     together on real data; it does not prove the bridge.
  D. Aggregate.  An independent dynamic program over count sequences decides
     the largest vertex count compatible with T <= 9214 - 35 v, for the proved
     premises alone and with each premise family added.

  python judge.py [--bridge-limit N]
"""
import argparse, gzip, itertools, json, os, subprocess, tempfile
from itertools import combinations
from pysat.card import CardEnc, EncType
from pysat.solvers import Glucose4

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
CERT = os.path.join(HERE, '..', 'certificates')
DATA = os.path.join(HERE, '..', 'data')


# ---------- cube geometry, written independently ----------
def nbrs(v):
    return [v ^ (1 << k) for k in range(9)]


def adjacent(a, b):
    return bin(a ^ b).count('1') == 1


def path_vertices(dirs):
    out = [0]
    for d in dirs:
        out.append(out[-1] ^ (1 << d))
    return out


def corners(c, prev, nxt):
    used = {(c ^ prev).bit_length() - 1, (c ^ nxt).bit_length() - 1}
    free = [k for k in range(9) if k not in used]
    return [c ^ (1 << a) ^ (1 << b) for a, b in combinations(free, 2)]


def is_cycle(vs):
    s = set(vs)
    return len(s) == len(vs) >= 4 and all(sum(adjacent(a, b) for b in s) == 2 for a in s) and connected(s)


def connected(s):
    s = set(s); start = next(iter(s)); seen = {start}; st = [start]
    while st:
        v = st.pop()
        for w in nbrs(v):
            if w in s and w not in seen:
                seen.add(w); st.append(w)
    return seen == s


# ---------- the judge's own encoding ----------
def encode(window, alpha, radius, cuts):
    """Return (clauses, var-of-vertex).  alpha entries: int or (lo, hi)."""
    centers = window[1:-1]
    ball = sorted(v for v in range(512) if min(bin(v ^ c).count('1') for c in centers) <= radius)
    B = set(ball)
    X = {v: i + 1 for i, v in enumerate(reversed(ball))}   # deliberately different order
    nv = len(ball)
    cls = [[X[v]] for v in window]
    endvars = []
    for v in ball:
        ns = [w for w in nbrs(v) if w in B]
        for t in combinations(ns, 3):
            cls.append([-X[v]] + [-X[w] for w in t])
        if len(ns) == 9:
            nv += 1; e = nv; endvars.append(e)
            cls.append([-X[v]] + [X[w] for w in ns])
            cls.append([-e, X[v]])
            for a, b in combinations(ns, 2):
                cls.append([-e, -X[a], -X[b]])
            for w in ns:
                cls.append([-X[v], e] + [X[t] for t in ns if t != w])

    def card(f, lits, bound, kind):
        nonlocal nv
        enc = f(lits=lits, bound=bound, top_id=nv, encoding=kind)
        nv = max(nv, enc.nv)
        cls.extend(enc.clauses)

    card(CardEnc.atmost, endvars, 2, EncType.totalizer)
    for i, c in enumerate(centers, 1):
        cs = [X[w] for w in corners(c, window[i - 1], window[i + 1])]
        a = alpha[i - 1]
        if a is None:
            continue
        lo, hi = (a, a) if isinstance(a, int) else a
        # absent corners in [lo, hi]  <=>  present corners in [21-hi, 21-lo]
        if 21 - lo < 21:
            card(CardEnc.atmost, cs, 21 - lo, EncType.seqcounter)
        if 21 - hi > 0:
            card(CardEnc.atleast, cs, 21 - hi, EncType.seqcounter)
    for v in ball:
        for a, b in combinations(range(9), 2):
            sq = [v, v ^ 1 << a, v ^ 1 << b, v ^ 1 << a ^ 1 << b]
            if v >> a & 1 == 0 and v >> b & 1 == 0 and all(w in B for w in sq):
                cls.append([-X[w] for w in sq])
        for t in combinations(range(9), 3):
            if any(v >> k & 1 for k in t):
                continue
            cube = [v ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
            if all(w in B for w in cube):
                for r in range(4):
                    cls.append([-X[cube[s]] for s in range(8) if s not in (r, 7 - r)])
    for cyc in cuts:
        assert is_cycle(cyc), cyc
        cls.append([-X[w] for w in cyc])
    return cls, X


# ---------- A and B ----------
def read_cnf(path):
    cls = []
    with gzip.open(path, 'rt') as f:
        for line in f:
            if line.startswith(('p', 'c')):
                continue
            lits = list(map(int, line.split()))[:-1]
            if lits:
                cls.append(lits)
    return cls


def audit_and_cuts(rec):
    """Classify stored vertex-only clauses; return the recorded cycle cuts."""
    window = rec['window']; centers = window[1:-1]
    ball = [v for v in range(512) if min(bin(v ^ c).count('1') for c in centers) <= rec['radius']]
    vert = {i + 1: v for i, v in enumerate(ball)}      # wincert numbering x_v = index+1
    cuts, counts, bad = [], {}, 0
    for cl in read_cnf(os.path.join(CERT, rec['case'] + '.cnf.gz')):
        if any(abs(l) not in vert for l in cl):
            continue                                        # involves auxiliary variables
        neg = [vert[-l] for l in cl if l < 0]; pos = [vert[l] for l in cl if l > 0]
        kind = None
        if len(cl) == 1 and pos:
            kind = 'window' if pos[0] in window else None
        elif len(neg) == 1 and sorted(pos) == sorted(nbrs(neg[0])):
            kind = 'selected_interior_has_neighbour'
        elif not pos:
            vs = neg
            if len(vs) == 4 and any(sum(adjacent(c, w) for w in vs if w != c) == 3 for c in vs):
                kind = 'degree'
            elif is_cycle(vs):
                kind = 'cycle%d' % len(vs) if (len(vs) == 4 or (len(vs) == 6 and in_three_face(vs))) else 'cycle_cut'
                if kind == 'cycle_cut':
                    cuts.append(vs)
        if kind is None:
            bad += 1
        else:
            counts[kind] = counts.get(kind, 0) + 1
    return cuts, counts, bad


def in_three_face(vs):
    x = 0
    for v in vs:
        x |= v ^ vs[0]
    return bin(x).count('1') <= 3


def refute(cls):
    with tempfile.TemporaryDirectory() as td:
        cnf, prf = os.path.join(td, 'f.cnf'), os.path.join(td, 'f.drup')
        nv = max(abs(l) for c in cls for l in c)
        with open(cnf, 'w') as f:
            f.write(f'p cnf {nv} {len(cls)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cls))
        with Glucose4(bootstrap_with=cls, with_proof=True) as s:
            if s.solve():
                return 'SAT', None
            open(prf, 'w').write('\n'.join(s.get_proof()) + '\n')
        drat = os.path.join(HERE, '..', '.build', 'drat-trim')
        if not os.path.exists(drat):
            from wincert import ensure_drat
            drat = ensure_drat()
        r = subprocess.run([drat, cnf, prf, '-t', '1800'], capture_output=True, text=True)
        return ('VERIFIED' if 's VERIFIED' in r.stdout else 'NOT VERIFIED'), len(cls)


# ---------- C ----------
def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m)); r.append(m[d])
    return tuple(r)


def bridge(limit):
    snakes = [e['vertex_sequence'] for e in json.load(open(os.path.join(ROOT, 'work', 'bank9.json')))]
    for f in ('outputs/square_counterexample.json', 'outputs/snake9_witness.json',
              'outputs/snake8_witness.json', 'outputs/short_maximal_witness.json'):
        try:
            d = json.load(open(os.path.join(ROOT, f)))
            if d.get('dimension', 9) == 9 and d.get('vertex_sequence'):
                snakes.append(d['vertex_sequence'])
        except (OSError, ValueError):
            pass
    tested = 0; failures = []
    for seq in snakes:
        S = set(seq)
        def alpha(i):
            return sum(w not in S for w in corners(seq[i], seq[i - 1], seq[i + 1]))
        al = [None] + [alpha(i) for i in range(1, len(seq) - 1)] + [None]
        for k in (3, 4):
            for i in range(1, len(seq) - k - 1 + 1):
                w = seq[i - 1:i + k + 1]
                if len(w) != k + 2 or i + k > len(seq) - 1:
                    continue
                ds = [(w[j] ^ w[j + 1]).bit_length() - 1 for j in range(k + 1)]
                lab = {}
                for d in ds:
                    lab.setdefault(d, len(lab))
                for d in range(9):
                    lab.setdefault(d, len(lab))
                tr = lambda v: sum(1 << lab[b] for b in range(9) if (v ^ w[0]) >> b & 1)
                W = [tr(v) for v in w]
                assert W == path_vertices(canon(ds))
                prio = min(al[i:i + k]) <= 4 or tested < limit
                if not prio:
                    continue
                cls, X = encode(W, al[i:i + k], 3, [])
                sel = {tr(v) for v in seq}
                units = [[X[v]] if v in sel else [-X[v]] for v in X]
                with Glucose4(bootstrap_with=cls + units) as s:
                    if not s.solve():
                        failures.append((seq[0], i, k))
                tested += 1
    return tested, failures


# ---------- D ----------
INF = 10 ** 9
FAMILIES = {
    'proved (Lean)': [],
    '+223': [(2, 2, 3)],
    '+224,232,323,41c': [(2, 2, 3), (2, 2, 4), (2, 3, 2), (3, 2, 3), (4, 1, 4), (4, 1, 5), (4, 1, 6)],
}


def max_vertices(triples, quads, K=10):
    bad3 = set(triples) | {t[::-1] for t in triples} | {(2, 2, 2)}
    bad4 = set(quads) | {q[::-1] for q in quads}
    pair = lambda a, b: not ((a == 1 and b <= 3) or (b == 1 and a <= 3))
    vals = range(1, K + 1)
    dp = {t: sum(t) for t in itertools.product(vals, repeat=3)
          if pair(t[0], t[1]) and pair(t[1], t[2]) and t not in bad3}
    best, n = None, 3
    while n <= 260:
        v = n + 2
        if min(dp.values()) + 8 <= 9214 - 35 * v:
            best = v
        nd = {}
        for (a, b, c), s in dp.items():
            for d in vals:
                if pair(c, d) and (b, c, d) not in bad3 and (a, b, c, d) not in bad4:
                    if s + d < nd.get((b, c, d), INF):
                        nd[(b, c, d)] = s + d
        dp = nd; n += 1
    return best


def reverify_index(path, workers=4):
    """Re-encode every case of a direction-certificate index independently and refute it."""
    from multiprocessing import Pool
    data = json.load(open(path))
    jobs = [(c['dirs'], [tuple(x) for x in c['alpha']], c['radius']) for c in data['cases']
            if c.get('drat_trim_verified')]
    with Pool(workers) as p:
        res = p.map(_reverify_one, jobs)
    return {'cases': len(jobs), 'verified': sum(r == 'VERIFIED' for r in res),
            'failures': [j[:2] for j, r in zip(jobs, res) if r != 'VERIFIED']}


def _reverify_one(arg):
    dirs, alpha, radius = arg
    window = path_vertices(dirs)
    al = [a if a[0] != a[1] else a[0] for a in alpha]
    cuts = []
    while True:
        cls, X = encode(window, al, radius, cuts)
        with Glucose4(bootstrap_with=cls) as s:
            if not s.solve():
                break
            model = s.get_model()
            sel = [v for v in X if model[X[v] - 1] > 0]
        cyc = [c for c in components_cycles(sel)]
        if not cyc:
            return 'SAT'
        cuts += cyc
    st, _ = refute(cls)
    return st


def components_cycles(sel):
    s = set(sel); seen = set(); out = []
    for v in sorted(s):
        if v in seen:
            continue
        comp, st = [], [v]
        while st:
            x = st.pop()
            if x in seen:
                continue
            seen.add(x); comp.append(x); st.extend(w for w in nbrs(x) if w in s)
        if len(comp) > 2 and all(sum(adjacent(x, w) for w in comp) == 2 for x in comp):
            out.append(sorted(comp))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bridge-limit', type=int, default=3000)
    ap.add_argument('--index', help='direction-certificate index to re-verify independently')
    a = ap.parse_args()
    if a.index:
        r = reverify_index(a.index)
        print(json.dumps(r))
        json.dump(r, open(os.path.join(DATA, 'judge_direction.json'), 'w'), indent=1)
        return
    meta = json.load(open(os.path.join(DATA, 'certificates.json')))
    verdict = {'A_reencoding': {}, 'B_clause_audit': {}, 'C_bridge': None, 'D_aggregate': {}}
    for rec in meta['cases']:
        cuts, counts, bad = audit_and_cuts(rec)
        verdict['B_clause_audit'][rec['case']] = {'classified': counts, 'unclassified': bad}
        al = [tuple(x) if isinstance(x, list) else x for x in rec['alpha']]
        cls, _ = encode(rec['window'], al, rec['radius'], cuts)
        st, n = refute(cls)
        verdict['A_reencoding'][rec['case']] = {'status': st, 'clauses': n, 'cycle_cuts_reused': len(cuts)}
        print(rec['case'], st, 'unclassified', bad, flush=True)
    tested, fails = bridge(a.bridge_limit)
    verdict['C_bridge'] = {'windows_tested': tested, 'failures': fails}
    print('bridge windows', tested, 'failures', len(fails), flush=True)
    for name, fam in FAMILIES.items():
        verdict['D_aggregate'][name] = max_vertices(fam, []) - 1
    verdict['D_aggregate']['+2423'] = max_vertices(FAMILIES['+224,232,323,41c'], [(2, 4, 2, 3)]) - 1
    ok = (all(v['status'] == 'VERIFIED' for v in verdict['A_reencoding'].values())
          and all(v['unclassified'] == 0 for v in verdict['B_clause_audit'].values())
          and not fails)
    verdict['overall'] = ('ACCEPT: premises refuted by two independent encodings and checked proofs; '
                          'bridge consistent with all tested windows' if ok else 'REJECT')
    json.dump(verdict, open(os.path.join(DATA, 'judge.json'), 'w'), indent=1)
    print(json.dumps(verdict['D_aggregate']), verdict['overall'])


if __name__ == '__main__':
    main()
