"""Repair a defective fixed-length walk while freeing both endpoints and all conflicts.

This is a restricted constructive experiment. Only an independently validated
witness establishes a lower bound; solver failure says nothing about the optimum.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'work'))
from neighborhood_search import model
from exact_search import cp_model
from check_snake import verify


def defects(vertices):
    duplicates, chords = [], []
    for j, v in enumerate(vertices):
        assert 0 <= v < 512
        if j:
            assert (v ^ vertices[j-1]).bit_count() == 1
        for i in range(j):
            if vertices[i] == v:
                duplicates.append((i, j))
            elif i+1 < j and (vertices[i] ^ v).bit_count() == 1:
                chords.append((i, j))
    return duplicates, chords


def run(source, radius, seconds, control=False):
    data = json.loads(source.read_text(encoding='utf-8'))
    path = data['best_valid_segment'] if control else data['best_walk']
    duplicates, chords = defects(path)
    conflict_positions = {i for pair in duplicates + chords for i in pair}
    released = {i for i in range(len(path)) if i < 10 or i >= len(path)-10
                or any(abs(i-j) <= radius for j in conflict_positions)}
    fixed = sorted(set(path) if control else {v for i, v in enumerate(path) if i not in released})
    target = len(path)-1
    m, xs, starts, arcs = model(9, target, list(set(path)), len(set(path)))
    for v in fixed:
        m.add(xs[v] == 1)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 2
    solver.parameters.random_seed = 196
    started = time.monotonic()
    status = solver.solve(m)
    out = {'source': source.relative_to(ROOT).as_posix(),
           'source_sha256': hashlib.sha256(source.read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
           'source_hash_normalization': 'CRLF to LF',
           'target_edges': target, 'radius_along_walk': radius,
           'endpoints_free': not control, 'control_fixed_valid_path': control,
           'fixed_vertices': fixed, 'released_positions': sorted(released) if not control else [],
           'input_duplicate_pairs': duplicates, 'input_chord_pairs': chords,
           'status': solver.status_name(status), 'seconds': time.monotonic()-started,
           'branches': solver.num_branches, 'conflicts': solver.num_conflicts,
           'scope': 'Frozen-fragment feasibility only; no global exclusion.'}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        result = [next(v for v, x in enumerate(starts) if solver.value(x))]
        while True:
            following = [v for (u,v), a in arcs.items() if u == result[-1] and solver.value(a)]
            if not following:
                break
            assert len(following) == 1 and following[0] not in result
            result.append(following[0])
        transitions = [(a^b).bit_length()-1 for a,b in zip(result,result[1:])]
        checked = verify(transitions, 9)
        assert checked['edges'] == target
        assert checked['vertex_sequence'] == [v ^ result[0] for v in result]
        assert set(fixed) <= set(result)
        out['witness'] = result
        out['independent_pairs_checked'] = checked['pairs_checked']
    elif control:
        raise AssertionError('Known valid path control failed: ' + out['status'])
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--radius', type=int, default=4)
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--control', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = run(args.source.resolve(), args.radius, args.seconds, args.control)
    args.output.write_text(json.dumps(out, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in
        ['witness','fixed_vertices','released_positions','input_chord_pairs','input_duplicate_pairs']}, indent=2))
