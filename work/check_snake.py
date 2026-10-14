import json
from collections import Counter
from pathlib import Path

TRANSITIONS = '''0 1 2 0 3 1 4 5 0 6 2 1 0 6 5 0 2 6 3 1 4 3 2 1 0 3 5 0 2 3 6 2 1 0 6 2 3 6 0 7 4 0 6 3 2 6 0 1 2 6 3 2 0 6 4 8 3 0 2 6 3 1 5 3 2 6 3 1 2 0 3 6 2 3 4 0 2 3 6 2 0 1 6 2 3 6 0 7 5 0 6 3 2 6 0 1 2 6 3 2 0 6 5 2 3 6 2 0 1 3 4 1 2 0 1 3 2 6 1 0 2 1 5 6 2 1 0 2 6 3 0 2 1 0 6 7 4 6 0 1 2 0 6 3 2 0 1 2 6 0 4 8 1 6 2 0 1 3 5 1 2 0 1 3 2 6 1 0 2 1 4 6 2 1 0 2 6 3 0 2 1 0 6 7 5 6 0 1 2 0 6'''

def verify(actions, n=9):
    vertices = [0]
    assert all(0 <= a < n for a in actions)
    for a in actions:
        vertices.append(vertices[-1] ^ (1 << a))
    assert len(set(vertices)) == len(vertices), 'Repeated vertex'
    pairs = 0
    for i, u in enumerate(vertices):
        for j in range(i + 1, len(vertices)):
            distance = (u ^ vertices[j]).bit_count()
            assert (distance == 1) == (j == i + 1), (i, j, distance)
            pairs += 1
    extensions = []
    blockers = []
    for endpoint in (vertices[0], vertices[-1]):
        for a in range(n):
            candidate = endpoint ^ (1 << a)
            adjacent_indices = [i for i, v in enumerate(vertices) if (v ^ candidate).bit_count() == 1]
            if candidate not in vertices and len(adjacent_indices) == 1:
                extensions.append([endpoint, candidate])
            blockers.append({'endpoint': endpoint, 'candidate': candidate,
                             'already_used': candidate in vertices,
                             'adjacent_path_indices': adjacent_indices})
    return {'edges': len(actions), 'vertices': len(vertices), 'pairs_checked': pairs,
            'coordinate_counts': dict(sorted(Counter(actions).items())),
            'endpoint_distance': (vertices[0] ^ vertices[-1]).bit_count(),
            'extensions': extensions, 'endpoint_checks': blockers,
            'vertex_sequence': vertices, 'transition_sequence': actions}

if __name__ == '__main__':
    result = verify(list(map(int, TRANSITIONS.split())))
    result['source'] = 'https://arxiv.org/html/2607.15270v3#A5'
    Path('outputs/snake9_witness.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in ('endpoint_checks','vertex_sequence','transition_sequence')}, indent=2))
