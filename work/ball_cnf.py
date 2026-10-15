"""Export the normalized ball model and its recorded cycle cuts as explicit CNF.

The encoding is transparent but its geometric soundness is not yet Lean-checked.
No preprocessing is used: fixed selection is represented by unit clauses.
"""
import json
from itertools import combinations
from pathlib import Path


def encode(data):
    radius = data['radius']
    assert data['endpoint_budget'] == 2
    ball = [v for v in range(512) if v.bit_count() <= radius]
    fixed = {0, 1, 2, 5, 10} | {
        (1 << a) | (1 << b) for a, b in combinations(range(2, 9), 2)
        if (a, b) != (2, 3)}
    variables = {f'x{v}': v + 1 for v in ball}
    next_id = 513
    clauses, reasons, ends = [], [], []

    def fresh(name):
        nonlocal next_id
        variables[name] = next_id
        next_id += 1
        return variables[name]

    def add(clause, reason):
        clauses.append(clause)
        reasons.append(reason)

    for v in ball:
        x = v + 1
        ns = [(v ^ (1 << k)) + 1 for k in range(9) if (v ^ (1 << k)) in ball]
        if v.bit_count() <= 2:
            add([x if v in fixed else -x], ['fixed', v])
        for triple in combinations(ns, 3):
            add([-x] + [-w for w in triple], ['degree_at_most_two', v])
        if v.bit_count() >= radius:
            continue
        add([-x] + ns, ['interior_positive_degree', v])
        if v.bit_count() <= 2:
            for w in ns:
                add([-x] + [t for t in ns if t != w], ['internal_degree_two', v])
        else:
            e = fresh(f'end{v}')
            ends.append(e)
            add([-e, x], ['endpoint_selected', v])
            for w in ns:
                add([-x, e] + [t for t in ns if t != w], ['degree_one_implies_endpoint', v])
            for a, b in combinations(ns, 2):
                add([-e, -a, -b], ['endpoint_degree_at_most_one', v])

    # Prefix counters: s1 and s2 mean at least one / at least two endpoints
    # have occurred. Forward implications suffice for the at-most-two bound.
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

    for cycle in data['cycle_clauses']:
        assert len(cycle) >= 4 and len(set(cycle)) == len(cycle)
        assert all(v in ball for v in cycle)
        assert all(sum((v ^ w).bit_count() == 1 for w in cycle) == 2 for v in cycle)
        add([-(v + 1) for v in cycle], ['cycle', cycle])
    return {'variables': variables, 'clauses': clauses, 'reasons': reasons,
            'radius': radius, 'endpoint_budget': 2,
            'scope': 'CNF encoding; geometry-to-CNF soundness remains unproved in Lean.'}


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', default='outputs/ball_certificate_seed.json')
    parser.add_argument('--output', default='outputs/ball_certificate.cnf')
    args = parser.parse_args()
    data = encode(json.loads(Path(args.input).read_text(encoding='utf-8')))
    target = Path(args.output)
    n = max(data['variables'].values())
    target.write_text(f'p cnf {n} {len(data["clauses"])}\n' + ''.join(
        ' '.join(map(str, c)) + ' 0\n' for c in data['clauses']), encoding='utf-8')
    target.with_suffix('.json').write_text(json.dumps(data, indent=2), encoding='utf-8')
    print(f'{n} variables, {len(data["clauses"])} clauses')
