"""Sanity check of the assignment `Tags.tau` of `LocalWindowTags.lean` on real snakes.

For the snakes of `work/bank9.json` and windows of consecutive path vertices of the
six canonical shapes, the window is moved to canonical position by a cube
automorphism; `S` is the moved vertex set, `E` the two moved endpoints.  The
assignment of `gen_lean_sat.py` (`.p v -> S v`, `.e v -> E v`, `.r c i j ->` at least
`j+1` of the first `i+1` counter literals hold) is then evaluated

1. on the full encoding built with the window's actual absent-corner counts: every
   clause must hold (this exercises every clause family and every register), and
2. on the UNSAT core of each certificate of the same shape (with the certificate's
   own meaning table): a clause may fail only if it is the final `over` clause of an
   absent-corner counter whose bound the real window violates.  Real snakes never
   match a certificate, so some bound is always violated.

  python3 test_lean_sat.py            # 4 windows per snake and shape
  python3 test_lean_sat.py --per 0    # every window
"""
import argparse, json, os, sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_lean_sat as G  # noqa: E402

ROOT = G.ROOT
SHAPES = {'repeated': [0, 1, 3, 7, 6], 'distinct': [0, 1, 3, 7, 15], 's01203': [0, 1, 3, 7, 6, 14],
          's01230': [0, 1, 3, 7, 15, 14], 's01234': [0, 1, 3, 7, 15, 31]}


def normalize(seg):
    """Cube automorphism moving the vertex list `seg` to a canonical window, or None."""
    x0 = seg[0]
    dirs = [(a ^ b).bit_length() - 1 for a, b in zip(seg, seg[1:])]
    perm = {}
    for d in dirs:
        if d not in perm:
            perm[d] = len(perm)
    for d in range(9):
        if d not in perm:
            perm[d] = len(perm)

    def phi(v):
        v ^= x0
        return sum(1 << perm[b] for b in range(9) if v >> b & 1)
    return phi


def absent(S, c, d1, d2):
    return sum(1 for a, b in combinations(range(9), 2)
               if a not in (d1, d2) and b not in (d1, d2) and (c ^ 1 << a ^ 1 << b) not in S)


def assignment(enc, S, E):
    tau = {}
    for x, m in enc.meaning.items():
        if m[0] == 'p':
            tau[x] = m[1] in S
        elif m[0] == 'e':
            tau[x] = m[1] in E

    def lit(l):
        return tau[l] if l > 0 else not tau[-l]
    pref = []
    for lits, k, kind in enc.ctrs:
        run, acc = 0, []
        for l in lits:
            run += lit(l)
            acc.append(run)
        pref.append(acc)
    for x, m in enc.meaning.items():
        if m[0] == 'r':
            tau[x] = pref[m[1]][m[2]] >= m[3] + 1
    return tau, lit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--per', type=int, default=4, help='windows per snake and shape (0 = all)')
    a = ap.parse_args()
    bank = json.load(open(os.path.join(ROOT, 'work', 'bank9.json')))
    certs = {}
    for f in sorted(os.listdir(G.CORE)):
        meta = json.load(open(os.path.join(G.CORE, f)))
        alpha = [b[0] if b[0] == b[1] else tuple(b) for b in meta['bounds']]
        enc = G.TaggedEncoding(meta['window'], alpha)
        nv, committed = G.read_cnf(os.path.join(G.CERTS, meta['name'] + '.cnf.gz'))
        npre = len(enc.clauses)
        core = [(committed[i - 1], enc.tags[i - 1] if i <= npre else ('cut',)) for i in meta['core_ids']]
        certs[meta['name']] = (meta, enc, core)
    full_cache = {}
    nwin = nfull = ncore = 0
    for snake in bank:
        path = snake['vertex_sequence']
        for shape, win in SHAPES.items():
            hits = []
            for i in range(len(path) - len(win) + 1):
                seg = path[i:i + len(win)]
                phi = normalize(seg)
                if [phi(v) for v in seg] == win:
                    hits.append(phi)
            if a.per and len(hits) > a.per:
                hits = [hits[j * len(hits) // a.per] for j in range(a.per)]
            for phi in hits:
                nwin += 1
                S = {phi(v) for v in path}
                E = {phi(path[0]), phi(path[-1])}
                cens = []
                for j in range(1, len(win) - 1):
                    c = win[j]
                    d1, d2 = (c ^ win[j - 1]).bit_length() - 1, (c ^ win[j + 1]).bit_length() - 1
                    cens.append(absent(S, c, d1, d2))
                key = (tuple(win), tuple(cens))
                if key not in full_cache:
                    full_cache[key] = G.TaggedEncoding(win, cens)
                enc = full_cache[key]
                tau, lit = assignment(enc, S, E)
                bad = [c for c in enc.clauses if not any(lit(l) for l in c)]
                assert not bad, (shape, cens, bad[:3])
                nfull += len(enc.clauses)
                for name, (meta, cenc, core) in certs.items():
                    if meta['window'] != win:
                        continue
                    tau, lit = assignment(cenc, S, E)
                    violated = set()
                    for ci, (lo, hi) in enumerate(meta['bounds']):
                        if cens[ci] > hi:
                            violated.add(('hi', ci))
                        if cens[ci] < lo:
                            violated.add(('lo', ci))
                    assert violated, (name, cens)  # real snakes avoid every certificate
                    for c, t in core:
                        ncore += 1
                        if not any(lit(l) for l in c):
                            assert t[0] == 'over' and cenc.ctrs[t[1]][2] in violated, (name, t, cens)
    print(f'{nwin} windows; {nfull} full-encoding clause evaluations and {ncore} core clause '
          f'evaluations passed ({len(full_cache)} distinct count vectors)')


if __name__ == '__main__':
    main()
