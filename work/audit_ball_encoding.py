"""Independent geometric audit of the concrete CNF core's clause shapes.

This Python audit is supplementary evidence. It is not the missing Lean bridge.
"""
import json
from itertools import combinations
from pathlib import Path

base = json.loads(Path('outputs/ball_direct.json').read_text(encoding='utf-8'))
core = json.loads(Path('outputs/ball_direct_core.json').read_text(encoding='utf-8'))
seed = json.loads(Path('outputs/ball_certificate_seed.json').read_text(encoding='utf-8'))
end_to_vertex = {value: int(name[3:]) for name, value in base['variables'].items()
                 if name.startswith('end')}
fixed = {0, 1, 2, 5, 10} | {2**a + 2**b for a, b in combinations(range(2, 9), 2)
                            if (a, b) != (2, 3)}
cycles = {frozenset(c) for c in seed['cycle_clauses']}
counts = {}
for clause, reason in zip(core['clauses'], core['reasons'], strict=True):
    kind, v = reason
    counts[kind] = counts.get(kind, 0) + 1
    assert len(clause) == len(set(clause))
    if kind == 'fixed':
        assert v.bit_count() <= 2
        assert clause == [v+1 if v in fixed else -(v+1)]
    elif kind == 'degree_at_most_two':
        assert clause[0] == -(v+1) and len(clause) == 4
        neighbors = [-lit-1 for lit in clause[1:]]
        assert all(lit < 0 for lit in clause)
        assert all((v ^ w).bit_count() == 1 for w in neighbors)
    elif kind in ('internal_degree_two', 'degree_one_implies_endpoint'):
        assert clause[0] == -(v+1)
        offset = 1 if kind == 'internal_degree_two' else 2
        if offset == 1:
            assert v.bit_count() <= 2
        else:
            assert end_to_vertex[clause[1]] == v and v.bit_count() < 5
        neighbors = [lit-1 for lit in clause[offset:]]
        assert len(neighbors) == 8
        assert all(lit > 0 for lit in clause[offset:])
        assert all((v ^ w).bit_count() == 1 for w in neighbors)
        assert all(w.bit_count() <= 5 for w in neighbors)
    elif kind == 'endpoint_degree_at_most_one':
        assert len(clause) == 3 and all(lit < 0 for lit in clause)
        assert end_to_vertex[-clause[0]] == v
        assert all((v ^ (-lit-1)).bit_count() == 1 for lit in clause[1:])
    elif kind == 'cycle':
        vertices = [-lit-1 for lit in clause]
        assert all(lit < 0 for lit in clause)
        assert frozenset(vertices) in cycles
        assert set(vertices) == set(v)
        assert all(sum((a ^ b).bit_count() == 1 for b in vertices) == 2 for a in vertices)
    elif kind == 'endpoint_triple':
        assert len(clause) == 3 and all(lit < 0 for lit in clause)
        assert sorted(-lit for lit in clause) == sorted(v)
        assert len({end_to_vertex[-lit] for lit in clause}) == 3
    else:
        raise AssertionError(kind)
print(json.dumps({'clauses_checked': len(core['clauses']), 'families': counts,
                  'status': 'Python clause-shape audit passed; Lean geometric bridge pending.'}, indent=2))
