"""Necessary local-ball conditions around a five-vertex induced path window.

The two canonical transition shapes are 0,1,2,0 and 0,1,2,3. A selected
internal center has its two forced path neighbors, so its singleton squares
are exactly the absent opposite corners in the other seven directions.
Solver exclusions require a separate certificate and geometric bridge.
"""
import argparse
import hashlib
import json
import time
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'work'))
from exact_search import cp_model
from low_singleton_radius3 import components


def run(radius, shape, alpha, seconds, fixed_selection=None):
    window = [0, 1, 3, 7, 6 if shape == 'repeated' else 15]
    centers = window[1:4]
    distance = lambda v: min((v ^ c).bit_count() for c in centers)
    ball = [v for v in range(512) if distance(v) <= radius]
    m = cp_model.CpModel()
    x = {v: m.new_bool_var(f'x{v}') for v in ball}
    endpoints = []
    for v in window:
        m.add(x[v] == 1)
    for v in ball:
        neighbors = [v ^ (1 << k) for k in range(9) if v ^ (1 << k) in x]
        degree = sum(x[w] for w in neighbors)
        if len(neighbors) == 9:
            e = m.new_bool_var(f'e{v}')
            endpoints.append(e)
            m.add(e <= x[v])
            m.add(degree == 2-e).only_enforce_if(x[v])
        else:
            m.add(degree <= 2).only_enforce_if(x[v])
        if fixed_selection is not None:
            m.add(x[v] == int(v in fixed_selection))
    m.add(sum(endpoints) <= 2)
    for i, center in enumerate(centers, 1):
        used = {(center ^ window[i-1]).bit_length()-1,
                (center ^ window[i+1]).bit_length()-1}
        pairs = [(a, b) for a, b in combinations(range(9), 2)
                 if a not in used and b not in used]
        assert len(pairs) == 21
        m.add(sum(x[center ^ (1 << a) ^ (1 << b)] for a, b in pairs) == 21-alpha[i-1])
    # These are valid induced-path restrictions, irrespective of connectedness.
    square_cuts = 0
    for v in ball:
        for a, b in combinations(range(9), 2):
            if v & (1 << a) or v & (1 << b):
                continue
            square = [v, v | (1 << a), v | (1 << b), v | (1 << a) | (1 << b)]
            if all(w in x for w in square):
                m.add(sum(x[w] for w in square) <= 3)
                square_cuts += 1
    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.random_seed = 41
    start = time.monotonic()
    cuts, iterations = [], []
    selected = None
    while True:
        remaining = seconds-(time.monotonic()-start)
        if remaining <= 0:
            status = cp_model.UNKNOWN
            break
        solver.parameters.max_time_in_seconds = remaining
        status = solver.solve(m)
        iterations.append({'status': solver.status_name(status),
                           'conflicts': solver.num_conflicts, 'branches': solver.num_branches})
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break
        selected = [v for v in ball if solver.value(x[v])]
        adj, parts = components(selected)
        cycles = [part['vertices'] for part in parts if part['cycle']]
        if not cycles:
            break
        for cycle in cycles:
            m.add(sum(x[v] for v in cycle) <= len(cycle)-1)
            cuts.append(cycle)
    result = {'radius': radius, 'shape': shape, 'window': window,
              'alpha_target': list(alpha), 'ball_size': len(ball),
              'status': solver.status_name(status), 'seconds_limit': seconds,
              'elapsed_seconds': time.monotonic()-start, 'workers': 1, 'seed': 41,
              'square_cuts': square_cuts, 'cycle_cuts': cuts, 'iterations': iterations,
              'fixed_selection_control': fixed_selection is not None,
              'code_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope': 'Local linear-forest relaxation; boundary vertices may be local endpoints. Infeasibility is not Lean-certified.'}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        s = set(selected)
        actual_alpha = [sum(all(w not in s for w in (c ^ (1 << a), c ^ (1 << b), c ^ (1 << a) ^ (1 << b)))
                            for a, b in combinations(range(9), 2)) for c in centers]
        assert actual_alpha == list(alpha)
        assert all(len(adj[v]) <= 2 for v in selected)
        interior = [v for v in selected if all(v ^ (1 << k) in x for k in range(9))]
        assert all(len(adj[v]) in (1, 2) for v in interior)
        assert sum(len(adj[v]) == 1 for v in interior) <= 2
        assert all(not part['cycle'] for part in parts)
        result.update(selected_vertices=selected, components=parts, alpha_checked=actual_alpha)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--radius', type=int, default=3)
    parser.add_argument('--shape', choices=['repeated', 'distinct'], default='repeated')
    parser.add_argument('--alpha', type=int, nargs=3, default=[2, 2, 3])
    parser.add_argument('--seconds', type=float, default=30)
    args = parser.parse_args()
    assert args.radius >= 2
    result = run(args.radius, args.shape, args.alpha, args.seconds)
    label = ''.join(map(str, args.alpha))
    target = Path(f'milestones/07-window-223/data/window_{label}_{args.shape}_r{args.radius}.json')
    target.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ['selected_vertices', 'components', 'cycle_cuts', 'iterations']}, indent=2))
