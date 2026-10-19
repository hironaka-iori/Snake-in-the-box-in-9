"""Search fixed-size induced vertex sets, eliminating cyclic components lazily."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'work'))
from exact_search import cp_model
from check_snake import verify


def components(vertices, n):
    selected = set(vertices)
    adj = {v: sorted(v^(1<<k) for k in range(n) if v^(1<<k) in selected) for v in selected}
    remaining, result = set(selected), []
    while remaining:
        todo, part = [min(remaining)], set()
        while todo:
            v = todo.pop()
            if v in part:
                continue
            part.add(v)
            todo.extend(adj[v])
        remaining -= part
        result.append(sorted(part))
    return result, adj


def run(args):
    n, target = args.n, args.edges
    assert n >= 1 and target >= 1
    size = 1<<n
    m = cp_model.CpModel()
    x = [m.new_bool_var(f'x{v}') for v in range(size)]
    end = [m.new_bool_var(f'e{v}') for v in range(size)]
    m.add(sum(x) == target+1)
    m.add(sum(end) == 2)
    for v in range(size):
        m.add(end[v] <= x[v])
        m.add(sum(x[v^(1<<k)] for k in range(n)) == 2-end[v]).only_enforce_if(x[v])
    # Translation to an endpoint and permutation of its first direction.
    m.add(end[0] == 1)
    m.add(x[1] == 1)
    squares = []
    if not args.no_squares:
        for a,b in itertools.combinations(range(n),2):
            for v in range(size):
                if (v & ((1<<a)|(1<<b))) == 0:
                    square = [v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)]
                    m.add(sum(x[w] for w in square) <= 3)
                    squares.append(square)
    hint = None
    if args.hint:
        d = json.loads(args.hint.read_text(encoding='utf-8'))
        hint = d['best_walk']
    if args.control:
        assert n == 9 and target == 191
        hint = json.loads((ROOT/'work/bank9.json').read_text())[0]['vertex_sequence']
        for v in range(size):
            m.add(x[v] == int(v in hint))
    if hint:
        for v in range(size):
            m.add_hint(x[v], int(v in hint))
    report = {'n': n, 'target_edges': target, 'control': args.control,
        'seed': args.seed, 'workers': args.workers, 'initial_square_cuts': len(squares),
        'hint': str(args.hint) if args.hint else None, 'rounds': [],
        'status': 'NOT_STARTED', 'scope': 'Constructive search; solver failures are not optimality certificates.'}
    started = time.monotonic()
    for iteration in range(args.rounds):
        remaining = args.seconds-(time.monotonic()-started)
        if remaining <= 0:
            break
        s = cp_model.CpSolver()
        s.parameters.num_search_workers = args.workers
        s.parameters.random_seed = args.seed
        s.parameters.max_time_in_seconds = min(args.round_seconds, remaining)
        status = s.solve(m)
        row = {'round': iteration, 'status': s.status_name(status), 'seconds': s.wall_time,
               'branches': s.num_branches, 'conflicts': s.num_conflicts}
        report['rounds'].append(row)
        report['status'] = row['status']
        if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
            break
        selected = [v for v in range(size) if s.value(x[v])]
        parts, adj = components(selected,n)
        assert len(selected) == target+1
        assert all(len(adj[v]) in (1,2) for v in selected)
        ends = [v for v in selected if len(adj[v]) == 1]
        assert len(ends) == 2 and 0 in ends
        path_parts = [c for c in parts if any(v in ends for v in c)]
        assert len(path_parts) == 1 and all(v in path_parts[0] for v in ends)
        cycles = [c for c in parts if c != path_parts[0]]
        assert all(all(len(adj[v]) == 2 for v in c) for c in cycles)
        row.update(selected_vertices=selected, components=parts, added_cycle_cuts=cycles)
        if not cycles:
            path = [0]
            while True:
                following = [w for w in adj[path[-1]] if len(path)<2 or w != path[-2]]
                if not following:
                    break
                assert len(following) == 1 and following[0] not in path
                path.append(following[0])
            checked = verify([(a^b).bit_length()-1 for a,b in zip(path,path[1:])],n)
            assert checked['edges'] == target and checked['vertex_sequence'] == path
            report['status'] = 'INDEPENDENTLY_CHECKED_WITNESS'
            report['witness'] = path
            report['pairs_checked'] = checked['pairs_checked']
            break
        for cycle in cycles:
            m.add(sum(x[v] for v in cycle) <= len(cycle)-1)
        m.clear_hints()
        for v in range(size):
            m.add_hint(x[v], int(v in selected))
    if report['rounds'] and report['rounds'][-1].get('added_cycle_cuts'):
        report['status'] = 'LIMIT_AFTER_ADDING_CUTS'
    report['total_seconds'] = time.monotonic()-started
    report['source_sha256_lf'] = hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
    if args.control:
        assert 'witness' in report
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'output':str(args.output),'status':report['status'],
        'rounds':len(report['rounds']),'seconds':report['total_seconds'],
        'components':[len(r.get('components',[])) for r in report['rounds']]}),flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=9)
    p.add_argument('--edges',type=int,default=196)
    p.add_argument('--rounds',type=int,default=100)
    p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--round-seconds',type=float,default=15)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--seed',type=int,default=196)
    p.add_argument('--hint',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--control',action='store_true')
    p.add_argument('--no-squares',action='store_true')
    run(p.parse_args())
