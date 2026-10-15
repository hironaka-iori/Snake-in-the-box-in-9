"""Explicit CNF encoding of a recorded three-center local window experiment.

Every cardinality constraint on the 21 opposite corners is expanded directly.
The input-clause interpretation still requires Lean verification.
"""
import argparse
import json
from itertools import combinations
from pathlib import Path


def encode(data, compact=False):
    window, radius, alpha = data['window'], data['radius'], data['alpha_target']
    centers = window[1:4]
    ball = [v for v in range(512) if min((v ^ c).bit_count() for c in centers) <= radius]
    vertices = set(ball)
    variables = {f'x{v}': v+1 for v in ball}
    clauses, reasons, ends = [], [], []
    next_id = 513

    def fresh(name):
        nonlocal next_id
        variables[name] = next_id
        next_id += 1
        return variables[name]

    def add(c, reason):
        clauses.append(c)
        reasons.append(reason)

    def negate(literal):
        return not literal if isinstance(literal, bool) else -literal

    def add_simplified(c, reason):
        if any(lit is True for lit in c):
            return
        c = list(dict.fromkeys(lit for lit in c if lit is not False))
        if any(-lit in c for lit in c):
            return
        add(c, reason)

    for v in window:
        add([v+1], ['window_selected', v])
    for v in ball:
        x = v+1
        ns = [(v ^ (1 << k))+1 for k in range(9) if v ^ (1 << k) in vertices]
        for a, b, c in combinations(ns, 3):
            add([-x, -a, -b, -c], ['degree_at_most_two', v])
        if len(ns) < 9:
            continue
        e = fresh(f'end{v}')
        ends.append(e)
        add([-x]+ns, ['interior_positive_degree', v])
        add([-e, x], ['endpoint_selected', v])
        for w in ns:
            add([-x, e]+[t for t in ns if t != w], ['degree_one_implies_endpoint', v])
        for a, b in combinations(ns, 2):
            add([-e, -a, -b], ['endpoint_degree_at_most_one', v])

    previous = None
    for i, e in enumerate(ends):
        s1, s2 = fresh(f'prefix{i}_1'), fresh(f'prefix{i}_2')
        add([-e, s1], ['counter_current', i])
        if previous is not None:
            p1, p2 = previous
            add([-p1, s1], ['counter_carry_one', i])
            add([-p2, s2], ['counter_carry_two', i])
            add([-e, -p1, s2], ['counter_increment', i])
            add([-e, -p2], ['counter_overflow', i])
        previous = s1, s2

    for i, center in enumerate(centers, 1):
        used = {(center ^ window[i-1]).bit_length()-1,
                (center ^ window[i+1]).bit_length()-1}
        corners = [(center ^ (1 << a) ^ (1 << b))+1
                   for a, b in combinations(range(9), 2) if a not in used and b not in used]
        assert len(corners) == 21 and all(c-1 in vertices for c in corners)
        k = alpha[i-1]
        if compact:
            previous_counts = [True]+[False]*(k+1)
            for index, corner in enumerate(corners, 1):
                counts = [True]
                for j in range(1, k+2):
                    s = fresh(f'missing{center}_{index}_{j}')
                    a, b, c = previous_counts[j], -corner, previous_counts[j-1]
                    # s iff a or (b and c), where b says the corner is absent.
                    for clause in ([negate(a), s], [negate(b), negate(c), s],
                                   [-s, a, b], [-s, a, c]):
                        add_simplified(clause, ['missing_counter', center, index, j])
                    counts.append(s)
                previous_counts = counts
            add([previous_counts[k]], ['missing_exact_lower', center, k])
            add([-previous_counts[k+1]], ['missing_exact_upper', center, k])
        else:
            for subset in combinations(corners, k+1):
                add(list(subset), ['at_most_missing', center, k])
            for subset in combinations(corners, 22-k):
                add([-c for c in subset], ['at_least_missing', center, k])

    for v in ball:
        for a, b in combinations(range(9), 2):
            if v & (1 << a) or v & (1 << b):
                continue
            square = [v, v | (1 << a), v | (1 << b), v | (1 << a) | (1 << b)]
            if all(w in vertices for w in square):
                add([-(w+1) for w in square], ['cycle', square])
    for cycle in data['cycle_cuts']:
        assert all(sum((a ^ b).bit_count() == 1 for b in cycle) == 2 for a in cycle)
        add([-(w+1) for w in cycle], ['cycle', cycle])
    return {'variables': variables, 'clauses': clauses, 'reasons': reasons,
            'window': window, 'radius': radius, 'alpha_target': alpha, 'compact': compact,
            'scope': 'Explicit local-window CNF; geometric interpretation not yet checked in Lean.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--shape', choices=['repeated', 'distinct'], required=True)
    parser.add_argument('--compact', action='store_true')
    args = parser.parse_args()
    source = Path(f'milestones/07-window-223/data/window_223_{args.shape}_r3.json')
    data = encode(json.loads(source.read_text(encoding='utf-8')), args.compact)
    suffix = 'compact' if args.compact else 'certificate'
    prefix = Path(f'milestones/07-window-223/data/window_223_{args.shape}_{suffix}')
    prefix.with_suffix('.json').write_text(json.dumps(data, separators=(',', ':')), encoding='utf-8')
    prefix.with_suffix('.cnf').write_text(
        f'p cnf {max(data["variables"].values())} {len(data["clauses"])}\n' +
        ''.join(' '.join(map(str, c))+' 0\n' for c in data['clauses']), encoding='utf-8')
    print(args.shape, len(data['clauses']), 'clauses')
