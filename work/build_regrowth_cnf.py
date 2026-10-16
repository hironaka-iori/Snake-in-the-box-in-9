"""Generate an untrusted necessary-condition CNF for fixed-prefix regrowth.

SAT/UNSAT results from this script are experiments until both the Boolean
certificate and the geometric interpretation have been checked by Lean.
Every clause has provenance, and counter wires have explicit count semantics.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def encode(path, keep=112, total_vertices=193):
    prefix = path[:keep]
    head = prefix[-1]
    banned = set().union(*({v} | {v ^ (1 << k) for k in range(9)} for v in prefix[:-1]))
    region, pending = set(), [head]
    while pending:
        v = pending.pop()
        for k in range(9):
            w = v ^ (1 << k)
            if w not in banned and w not in region:
                region.add(w)
                pending.append(w)
    region.add(head)
    vertices = sorted(region)
    n = len(vertices)
    selected = {v: i + 1 for i, v in enumerate(vertices)}
    endpoints = {v: n + i + 1 for i, v in enumerate(vertices)}
    clauses, reasons, counters = [], [], []
    next_id = 2 * n + 1
    target = total_vertices - keep + 1

    def add(clause, kind, **info):
        clauses.append(clause)
        reasons.append(dict(kind=kind, **info))

    for v in vertices:
        x, e = selected[v], endpoints[v]
        neighbors = [w for w in vertices if (v ^ w).bit_count() == 1]
        ns = [selected[w] for w in neighbors]
        add([-e, x], 'endpoint_selected', vertex=v)
        add([-x] + ns, 'neighbor_exists', vertex=v, neighbors=neighbors)
        for a, b, c in combinations(neighbors, 3):
            add([-x, -selected[a], -selected[b], -selected[c]], 'degree_two', vertices=[v, a, b, c])
        for a, b in combinations(neighbors, 2):
            add([-e, -selected[a], -selected[b]], 'endpoint_degree_one', vertices=[v, a, b])
        for a in neighbors:
            add([-x, e] + [selected[b] for b in neighbors if a != b],
                'other_neighbor', vertex=v, excluded=a, neighbors=neighbors)
        if v == head:
            add([x], 'head_selected')
            add([e], 'head_endpoint')

    def atmost(literals, bound, label):
        nonlocal next_id
        if bound >= len(literals):
            return
        if bound < 0:
            add([], 'negative_bound', label=label)
            return

        def tree(leaves):
            nonlocal next_id
            if len(leaves) <= 1:
                return leaves
            split = len(leaves) // 2
            left, right = tree(leaves[:split]), tree(leaves[split:])
            out = list(range(next_id, next_id + min(bound + 1, len(leaves))))
            next_id += len(out)
            counters.append(dict(outputs=out, leaves=leaves))
            for i in range(len(left) + 1):
                for j in range(len(right) + 1):
                    if 0 < i + j <= len(out):
                        add(([-left[i-1]] if i else []) + ([-right[j-1]] if j else []) + [out[i+j-1]],
                            'counter_merge', left=left, right=right, outputs=out, i=i, j=j)
            return out

        out = tree(literals)
        add([-out[bound]], 'counter_bound', label=label, leaves=literals, bound=bound)

    others = []
    for v in vertices:
        if v != head:
            others.append(endpoints[v])
            if (v.bit_count() ^ head.bit_count()) % 2 != (target - 1) % 2:
                add([-endpoints[v]], 'endpoint_parity', vertex=v)
    atmost(others, 1, 'other_endpoints')
    add(others, 'other_endpoint_exists')
    for parity in (0, 1):
        side = [selected[v] for v in vertices if v.bit_count() % 2 == parity]
        count = target // 2 + int(target % 2 == 1 and parity == head.bit_count() % 2)
        atmost(side, count, f'selected_parity_{parity}')
        atmost([-v for v in side], len(side) - count, f'absent_parity_{parity}')
    for v in vertices:
        for a, b in combinations(range(9), 2):
            if v & (1 << a) or v & (1 << b):
                continue
            square = [v, v ^ (1 << a), v ^ (1 << b), v ^ (1 << a) ^ (1 << b)]
            if all(w in selected for w in square):
                add([-selected[w] for w in square], 'square', vertices=square)
    return dict(clauses=clauses, reasons=reasons, variables=next_id-1,
                vertices=vertices, head=head, banned=sorted(banned), prefix=prefix,
                selected=selected, endpoints=endpoints, counters=counters,
                target=target, total_vertices=total_vertices,
                scope='Untrusted necessary-condition encoding; geometric Lean proof required.')


def witness_assignment(data, suffix):
    """Interpret every counter by its intended integer count, not a SAT solver."""
    assignment = {}
    for v, i in data['selected'].items():
        assignment[i] = v in suffix
    for v, i in data['endpoints'].items():
        assignment[i] = v in (suffix[0], suffix[-1])
    for counter in data['counters']:
        count = sum(assignment[abs(lit)] == (lit > 0) for lit in counter['leaves'])
        for threshold, wire in enumerate(counter['outputs'], 1):
            assignment[wire] = count >= threshold
    failed = [i for i, clause in enumerate(data['clauses'])
              if not any(assignment[abs(lit)] == (lit > 0) for lit in clause)]
    return assignment, failed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--entry', type=int, default=0)
    parser.add_argument('--keep', type=int, default=112)
    parser.add_argument('--total-vertices', type=int, default=193)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--audit-bank', action='store_true')
    args = parser.parse_args()
    bank = [r['vertex_sequence'] for r in json.loads((ROOT/'work/bank9.json').read_text())]
    oriented = [p for s in bank for p in (s, s[::-1])]
    if not 2 <= args.keep <= min(map(len, oriented)):
        parser.error('keep must leave a nonempty prefix and suffix')
    if args.audit_bank:
        records = []
        for entry, path in enumerate(oriented):
            data = encode(path, args.keep, len(path))
            assignment, failed = witness_assignment(data, path[args.keep-1:])
            if failed:
                raise RuntimeError(f'Known witness rejected at entry {entry}: {failed[:10]}')
            records.append(dict(entry=entry, variables=len(assignment), clauses=len(data['clauses'])))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(dict(status='passed', entries=records,
            scope='Executable positive controls, not formal verification.'), indent=2)+'\n')
        print(f'{len(records)} known witnesses satisfy every generated clause and counter')
        return
    data = encode(oriented[args.entry], args.keep, args.total_vertices)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_suffix('.json').write_text(json.dumps(data, separators=(',', ':'))+'\n')
    args.output.with_suffix('.cnf').write_text(f"p cnf {data['variables']} {len(data['clauses'])}\n" +
        ''.join(' '.join(map(str, clause))+' 0\n' for clause in data['clauses']))
    print(f"entry={args.entry} vertices={len(data['vertices'])} clauses={len(data['clauses'])}")


if __name__ == '__main__':
    main()
