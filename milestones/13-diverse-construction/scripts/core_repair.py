"""Constructive repair using solver assumption cores; no optimality inference."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'work'))
sys.path.insert(0, str(ROOT/'milestones/12-construction-196/scripts'))
from neighborhood_search import model
from exact_search import cp_model
from repair_walk import defects
from check_snake import verify


def minimum_cover(edges):
    """Exact branching on at most a few recorded conflict edges."""
    if not edges:
        return set()
    a, b = edges[0]
    choices = []
    for v in (a, b):
        choices.append({v} | minimum_cover([e for e in edges if v not in e]))
    return min(choices, key=lambda s: (len(s), sorted(s)))


def run(args):
    source = args.source.resolve()
    data = json.loads(source.read_text(encoding='utf-8'))
    walk = data['best_valid_segment'] if args.control else (
        data['best_walk'] if args.member < 0 else data['pool'][args.member])
    duplicates, chords = defects(walk)
    assert not duplicates, 'This experiment requires a distinct-vertex walk.'
    target = len(walk)-1
    released = minimum_cover(chords)
    assert all(i in released or j in released for i, j in chords)
    fixed = {v for i, v in enumerate(walk) if i not in released}
    positions = {v: i for i, v in enumerate(walk)}
    m, xs, starts, arcs = model(9, target, walk, len(walk))
    index_to_vertex = {x.index: v for v, x in enumerate(xs)}
    rng = random.Random(args.seed)
    report = {
        'source': source.relative_to(ROOT).as_posix(), 'source_hash_normalization': 'CRLF to LF',
        'source_sha256': hashlib.sha256(source.read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
        'member': args.member, 'control': args.control, 'target_edges': target,
        'policy': args.policy, 'seed': args.seed, 'initial_cover_positions': sorted(released),
        'chord_pairs': chords, 'rounds': [], 'status': 'NOT_STARTED',
        'scope': 'Restricted fixed-vertex feasibility; assumption cores are solver output, not Lean certificates.'}
    started = time.monotonic()
    for iteration in range(args.rounds):
        remaining = args.total_seconds - (time.monotonic()-started)
        if remaining <= 0:
            break
        m.clear_assumptions()
        m.add_assumptions([xs[v] for v in sorted(fixed)])
        s = cp_model.CpSolver()
        s.parameters.num_search_workers = 1
        s.parameters.random_seed = args.seed
        s.parameters.max_time_in_seconds = min(args.round_seconds, remaining)
        status = s.solve(m)
        row = {'round': iteration, 'fixed_vertices': sorted(fixed),
               'status': s.status_name(status), 'seconds': s.wall_time,
               'branches': s.num_branches, 'conflicts': s.num_conflicts}
        report['rounds'].append(row)
        report['status'] = row['status']
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            path = [next(v for v, x in enumerate(starts) if s.value(x))]
            while True:
                following = [v for (u, v), a in arcs.items() if u == path[-1] and s.value(a)]
                if not following:
                    break
                assert len(following) == 1 and following[0] not in path
                path.append(following[0])
            verified = verify([(a^b).bit_length()-1 for a,b in zip(path,path[1:])], 9)
            assert verified['edges'] == target and fixed <= set(path)
            assert verified['vertex_sequence'] == [v^path[0] for v in path]
            report['witness'] = path
            report['pairs_checked'] = verified['pairs_checked']
            break
        if status != cp_model.INFEASIBLE:
            break
        core = [index_to_vertex[k] for k in s.sufficient_assumptions_for_infeasibility()]
        assert set(core) <= fixed
        row['core_vertices'] = core
        if not core:
            report['status'] = 'EMPTY_CORE_REQUIRES_SEPARATE_AUDIT'
            break
        if args.control:
            raise AssertionError('Known valid path was rejected')
        if args.policy == 'block':
            pick = min(core, key=lambda v: (min((abs(positions[v]-j) for j in released), default=0), v))
            drop = {v for v in fixed if abs(positions[v]-positions[pick]) <= 2}
        else:
            drop = set(rng.sample(sorted(core), min(5, len(core))))
        assert drop and drop <= fixed and drop & set(core)
        row['released_vertices'] = sorted(drop)
        released.update(positions[v] for v in drop)
        fixed -= drop
    report['total_seconds'] = time.monotonic()-started
    if report['rounds'] and report['rounds'][-1].get('released_vertices'):
        # The last relaxation has not been solved yet.
        report['status'] = 'ROUND_LIMIT_AFTER_RELAXATION'
    report['remaining_fixed_vertices'] = sorted(fixed)
    if args.control:
        assert 'witness' in report
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'output': str(args.output), 'status': report['status'],
                      'rounds': len(report['rounds']), 'fixed': len(fixed),
                      'seconds': report['total_seconds']}), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--member', type=int, default=-1)
    p.add_argument('--policy', choices=('block', 'scattered'), default='block')
    p.add_argument('--seed', type=int, default=196)
    p.add_argument('--rounds', type=int, default=40)
    p.add_argument('--round-seconds', type=float, default=10)
    p.add_argument('--total-seconds', type=float, default=60)
    p.add_argument('--control', action='store_true')
    run(p.parse_args())
