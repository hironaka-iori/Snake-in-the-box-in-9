"""Aggregate consequences of the local-window survey.

1. Minimum mean singleton count over sequences whose internal triples are
   feasible in some window shape (Karp's algorithm; values above K lumped).
2. The small forbidden-pattern family used in Lean, and its own minimum mean.
3. The integer potential, checked against `potC` in WindowPotential242.lean.
4. The exact minimum of T for each vertex count, against T + 2*s0 = 9214 - 35v.

  python aggregate.py --survey ../data/survey_c3_r3.json
"""
import argparse, itertools, json, os, re
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..', '..', '..', 'work', 'spectral', 'stronger', 'WindowPotential242.lean')
LEAN4 = os.path.join(HERE, '..', '..', '..', 'work', 'spectral', 'stronger', 'WindowPotential241.lean')
QUADS = {(2, 4, 2, 3), (3, 2, 4, 2)}   # certified four-center exclusion
INF = 10 ** 6
# Forbidden internal triples assumed by Aggregate242Conditional (with reversals).
# The first two families are already Lean theorems; (2,2,2) is too.
PATTERNS = [((1, 1), (1, 3), (1, INF)),   # count-one neighbour has count >= 4 (Lean)
            ((2, 2), (2, 2), (2, 4)),     # 222 (Lean), 223, 224 (certified)
            ((2, 2), (3, 3), (2, 2)),     # 232 (certified)
            ((3, 3), (2, 2), (3, 3)),     # 323 (certified)
            ((4, 4), (1, 1), (4, 6))]     # 41c, 4<=c<=6 (certified)


def forbidden(t, pats=PATTERNS):
    pats = pats + [p[::-1] for p in pats]
    return any(all(lo <= x <= hi for x, (lo, hi) in zip(t, p)) for p in pats)


def min_mean(ok, K):
    vals = range(1, K + 2)
    states = [(a, b) for a in vals for b in vals]
    idx = {s: i for i, s in enumerate(states)}
    edges = [(idx[(a, b)], idx[(b, c)], c) for a in vals for b in vals for c in vals
             if any(v > K for v in (a, b, c)) or ok((a, b, c))]
    n = len(states)
    D = [[INF] * n for _ in range(n + 1)]
    D[0] = [0] * n
    for k in range(1, n + 1):
        for u, w, c in edges:
            if D[k - 1][u] + c < D[k][w]:
                D[k][w] = D[k - 1][u] + c
    best = None
    for v in range(n):
        if D[n][v] >= INF:
            continue
        worst = max(Fr(D[n][v] - D[k][v], n - k) for k in range(n) if D[k][v] < INF)
        best = worst if best is None else min(best, worst)
    return best


def potential(K=6):
    """Longest-path potential for weight 14 - 5z; values above K clamp to K+1."""
    V = range(1, K + 2)
    pair_ok = lambda a, b: not ((a == 1 and b <= 3) or (b == 1 and a <= 3))
    states = [(a, b) for a in V for b in V if pair_ok(a, b)]
    P = {s: 0 for s in states}
    for _ in range(1000):
        changed = False
        for (x, y) in states:
            for z in V:
                if (y, z) in P and not forbidden((x, y, z)):
                    val = P[(x, y)] + 14 - 5 * z
                    if val > P[(y, z)]:
                        P[(y, z)] = val; changed = True
        if not changed:
            return P
    raise RuntimeError('positive cycle: mean below 14/5')


def min_mean_quads(K=7):
    """Minimum mean with the triple patterns and the quadruple exclusion (triple states)."""
    vals = range(1, K + 2)
    pair = lambda a, b: not ((a == 1 and b <= 3) or (b == 1 and a <= 3))
    states = [t for t in itertools.product(vals, repeat=3)
              if pair(t[0], t[1]) and pair(t[1], t[2]) and not forbidden(t)]
    idx = {s: i for i, s in enumerate(states)}
    edges = [(idx[s], idx[s[1:] + (d,)], d) for s in states for d in vals
             if s[1:] + (d,) in idx and s + (d,) not in QUADS]
    n = len(states)
    D = [[INF] * n for _ in range(n + 1)]
    D[0] = [0] * n
    for k in range(1, n + 1):
        for u, w, c in edges:
            if D[k - 1][u] + c < D[k][w]:
                D[k][w] = D[k - 1][u] + c
    return min(max(Fr(D[n][v] - D[k][v], n - k) for k in range(n) if D[k][v] < INF)
               for v in range(n) if D[n][v] < INF)


def potential3(K=6):
    """Potential on triples for weight 3 - w, initialised so that base triples sum to 9."""
    V = range(1, K + 2)
    pair = lambda a, b: not ((a == 1 and b <= 3) or (b == 1 and a <= 3))
    states = [t for t in itertools.product(V, repeat=3)
              if pair(t[0], t[1]) and pair(t[1], t[2]) and not forbidden(t)]
    P = {s: max(0, 9 - sum(s)) for s in states}
    for _ in range(1000):
        changed = False
        for s in states:
            for d in V:
                t = s[1:] + (d,)
                if t in P and s + (d,) not in QUADS and P[s] + 3 - d > P[t]:
                    P[t] = P[s] + 3 - d; changed = True
        if not changed:
            return P
    raise RuntimeError('positive cycle: mean below 3')


def exact_min_T(v, K=10, quads=False):
    """Minimum T over count sequences of length v (endpoints >= 4)."""
    vals = range(1, K + 1)
    pair = lambda a, b: not ((a == 1 and b <= 3) or (b == 1 and a <= 3))
    dp = {(a, b, c): a + b + c for a, b, c in itertools.product(vals, repeat=3)
          if pair(a, b) and pair(b, c) and not forbidden((a, b, c))}
    for _ in range(3, v - 2):
        nd = {}
        for (a, b, c), s in dp.items():
            for d in vals:
                if quads and (a, b, c, d) in QUADS:
                    continue
                if pair(c, d) and not forbidden((b, c, d)) and s + d < nd.get((b, c, d), INF):
                    nd[(b, c, d)] = s + d
        dp = nd
    return min(dp.values()) + 8


def lean_table():
    src = open(LEAN, encoding='utf-8').read()
    body = src[src.index('def potC'):src.index('def pot (a b')]
    return {(int(a), int(b)): int(c) for a, b, c in re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*(\d+)', body)}


def lean_table3():
    src = open(LEAN4, encoding='utf-8').read()
    body = src[src.index('def potC3'):src.index('def pot3 (a b c')]
    return {(int(a), int(b), int(c)): int(d) for a, b, c, d in
            re.findall(r'\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*(\d+)', body)}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--survey', required=True)
    ap.add_argument('--out', default=os.path.join(HERE, '..', 'data', 'aggregate.json'))
    a = ap.parse_args()
    data = json.load(open(a.survey))
    feasible = {tuple(r['alpha']) for r in data['results'] if r['status'] != 'UNSAT'}
    K = max(max(r['alpha']) for r in data['results'])
    survey_mean = min_mean(lambda t: t in feasible, K)
    pattern_mean = min_mean(lambda t: not forbidden(t), 8)
    # every triple the patterns forbid must be refuted in the survey (both shapes)
    refuted = {}
    for r in data['results']:
        refuted.setdefault(tuple(r['alpha']), []).append(r['status'] == 'UNSAT')
    unsupported = [t for t, v in refuted.items() if forbidden(t) and not all(v)]
    P = potential()
    lean = lean_table()
    nonzero = {s: p for s, p in P.items() if p}
    assert nonzero == lean, (nonzero, lean)
    P3 = potential3()
    assert {s: p for s, p in P3.items() if p} == lean_table3()
    rows = [(v, exact_min_T(v), 9214 - 35 * v) for v in range(240, 248)]
    rows4 = [(v, exact_min_T(v, quads=True), 9214 - 35 * v) for v in range(238, 246)]
    vmax = max(v for v, t, cap in rows if t <= cap)
    vmax4 = max(v for v, t, cap in rows4 if t <= cap)
    out = {'survey_min_mean': str(survey_mean), 'pattern_min_mean': str(pattern_mean),
           'patterns_not_refuted_in_survey': unsupported, 'max_potential': max(P.values()),
           'potential_matches_lean': True, 'exact_rows_triples': rows, 'max_vertices': vmax,
           'max_edges': vmax - 1, 'quadruple_exclusion': sorted(QUADS),
           'min_mean_with_quadruples': str(min_mean_quads()), 'max_potential3': max(P3.values()),
           'potential3_matches_lean': True, 'exact_rows_with_quadruples': rows4,
           'max_vertices_with_quadruples': vmax4, 'max_edges_with_quadruples': vmax4 - 1}
    json.dump(out, open(a.out, 'w'), indent=1)
    print(json.dumps(out, indent=1))
