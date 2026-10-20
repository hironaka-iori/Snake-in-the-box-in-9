"""Bounded, resumable research experiments; no result here is a Lean theorem.

Run from the repository root with Python >=3.12 and OR-Tools 9.15.6755.
Output is append-only by run id. Each case has a result, log, inputs and hashes.
"""
import argparse
import hashlib
import itertools as it
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
BASE = "ad5a7862c52ea1d7345aec8d94c1d2fdc6ede206"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, obj):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def now():
    return datetime.now(timezone.utc).isoformat()


def faces(n):
    for a, b in it.combinations(range(n), 2):
        for q in range(1 << n):
            if not q & ((1 << a) | (1 << b)):
                yield (a, b, q), (q, q ^ (1 << a), q ^ (1 << b), q ^ (1 << a) ^ (1 << b))


def check_path(path, n):
    assert path and len(set(path)) == len(path)
    assert all(0 <= v < (1 << n) for v in path)
    for i, x in enumerate(path):
        for j in range(i + 1, len(path)):
            assert ((x ^ path[j]).bit_count() == 1) == (j == i + 1), (i, j)


def census(path, n, details=False):
    check_path(path, n)
    sel = set(path)
    alpha = {x: 0 for x in path}
    empty = []
    max_touch = 0
    saturated_homogeneous = []
    for (a, b, q), face in faces(n):
        occ = sel.intersection(face)
        if len(occ) == 1:
            alpha[next(iter(occ))] += 1
        if not occ:
            shell = {x ^ (1 << k) for x in face for k in range(n) if k not in (a, b)}
            touched = sel & shell
            max_touch = max(max_touch, len(touched))
            empty.append((a, b, q))
            if n >= 3 and len(touched) == 3 * (n - 2):
                missing = []
                for k in range(n):
                    if k not in (a, b):
                        absent = [x for x in face if (x ^ (1 << k)) not in sel]
                        assert len(absent) == 1
                        missing.append(absent[0])
                if len({x.bit_count() % 2 for x in missing}) == 1:
                    assert len(path) == 4 * (n - 2) - 1
                    saturated_homogeneous.append([a, b, q])
    T = sum(alpha.values())
    E = 4 * len(empty)
    v = len(path)
    # General-dimension identity rederived, valid only for v>=2.
    if v >= 2:
        assert E + 2 * T + (n * (n - 1) - 2) * v == n * (n - 1) * 2 ** (n - 1) - 4
    assert max_touch <= 3 * (n - 2)
    out = {"n": n, "v": v, "edges": v - 1, "E": E, "s0": len(empty), "T": T,
           "alpha_min": min(alpha.values()), "alpha_max": max(alpha.values()),
           "max_empty_face_touch": max_touch,
           "homogeneous_saturated_faces": saturated_homogeneous}
    if details:
        out.update(path=path, alpha=[alpha[x] for x in path], empty_faces=empty)
    return out


def sharp_path(n):
    # Q={0,1,2,3}; every normal translate misses corner 0.
    path = []
    for j, k in enumerate(range(2, n)):
        corners = [1, 3, 2] if j % 2 == 0 else [2, 3, 1]
        if path:
            path.append(corners[0] ^ (1 << (k - 1)) ^ (1 << k))
        path.extend(c ^ (1 << k) for c in corners)
    return path


def exhaustive(n):
    count, maxv, sharp = 0, 0, 0
    def visit(path, mask):
        nonlocal count, maxv, sharp
        c = census(path, n)
        count += 1
        maxv = max(maxv, len(path))
        sharp += bool(c['homogeneous_saturated_faces'])
        last = path[-1]
        for k in range(n):
            y = last ^ (1 << k)
            if mask >> y & 1:
                continue
            if any(mask >> (y ^ (1 << l)) & 1 for l in range(n) if (y ^ (1 << l)) != last):
                continue
            visit(path + [y], mask | (1 << y))
    visit([0], 1)
    return {"dimension": n, "rooted_ordered_paths": count, "max_vertices": maxv,
            "paths_with_homogeneous_saturation": sharp,
            "scope": "Every ordered induced path rooted at 0; translation covers every path."}


def canon(ds):
    names = {}
    return tuple(names.setdefault(d, len(names)) for d in ds)


def window_key(ds, counts):
    bounds = tuple((x, x) if x < 6 else (6, 21) for x in counts)
    return min((canon(ds), bounds), (canon(ds[::-1]), bounds[::-1]))


def induced(ds):
    p = [0]
    for d in ds:
        p.append(p[-1] ^ (1 << d))
    try:
        check_path(p, 9)
        return True
    except AssertionError:
        return False


def extract_cycle():
    data = ROOT / 'milestones/10-window-aggregate/data'
    known = {}
    for ln in (data / 'oracle_cache.jsonl').read_text().splitlines():
        x = json.loads(ln)
        if x['radius'] == 3:
            known[(tuple(x['dirs']), tuple(map(tuple, x['alpha'])))] = x['status']
    for fn in ['survey_c3_r3.json', 'survey_c4_r3_k5.json']:
        for x in json.loads((data / fn).read_text())['results']:
            known.setdefault(window_key(x['directions'], x['alpha']), x['status'])
    # The frozen 175-exclusion index is separately checked below.
    forbidden = {(tuple(x['dirs']), tuple(map(tuple, x['alpha'])))
                 for x in json.loads((data / 'direction_certificates_k5p.json').read_text())['cases']}
    shapes = [()]
    for _ in range(7):
        shapes = [s + (d,) for s in shapes for d in range(max(s, default=-1) + 2) if induced(s + (d,))]
    assert len(shapes) == 34
    counts = [2, 3, 6, 2, 2, 6]
    graph = {}
    for shape in shapes:
        for phase in range(6):
            out = []
            for d in range(max(shape) + 2):
                ds = shape + (d,)
                if not induced(ds):
                    continue
                keys = [window_key(ds[-c-1:], [counts[(phase-c+1+t) % 6] for t in range(c)])
                        for c in range(2, 6)]
                if not any(k in forbidden or known.get(k) == 'UNSAT' for k in keys):
                    out.append(((canon(ds[1:]), (phase + 1) % 6), d, keys))
            graph[(shape, phase)] = out
    active, done, stack, edges = {}, set(), [], []
    found = None
    def dfs(u):
        nonlocal found
        active[u] = len(stack)
        stack.append(u)
        for v, d, keys in graph[u]:
            if found:
                break
            if v in active:
                j = active[v]
                found = edges[j:] + [(u, v, d, keys)]
                break
            if v not in done:
                edges.append((u, v, d, keys))
                dfs(v)
                edges.pop()
        stack.pop()
        active.pop(u)
        done.add(u)
    for u in graph:
        if not found and u not in done:
            dfs(u)
    assert found, 'No cycle found for the saved extremal counts'
    cs = [counts[u[1]] for u, v, d, keys in found]
    assert 2 * sum(cs) == 7 * len(cs)
    return {'status': 'CYCLE_FOUND', 'counts': cs,
            'edges': [{'shape': list(u[0]), 'phase': u[1], 'next_shape': list(v[0]), 'append_label': d,
                       'count': counts[u[1]],
                       'window_statuses': [known.get(k, 'UNTESTED') for k in keys]}
                      for u, v, d, keys in found],
            'mean': '7/2', 'frozen_175_windows_avoided': True,
            'inputs': {str((data/f).relative_to(ROOT)): sha(data/f) for f in
                       ['oracle_cache.jsonl', 'survey_c3_r3.json', 'survey_c4_r3_k5.json',
                        'direction_certificates_k5p.json']}}


def lift_cycle(cycle, target=45, seconds=12, nodes=200000):
    initial = cycle['edges'][0]['shape']
    path = [0]
    for d in initial:
        path.append(path[-1] ^ (1 << d))
    best = (path[:], initial[:], [])
    visits, stopped = 0, None
    start = time.monotonic()
    def rec(path, dirs, cs):
        nonlocal visits, best, stopped
        visits += 1
        if len(path) > len(best[0]):
            best = (path[:], dirs[:], cs[:])
        if len(path) - 1 >= target:
            stopped = 'TARGET_REACHED'
            return
        if visits >= nodes or time.monotonic() - start >= seconds:
            stopped = 'UNKNOWN_LIMIT'
            return
        edge = cycle['edges'][len(cs) % len(cycle['edges'])]
        hist = dirs[-7:]
        assert list(canon(hist)) == edge['shape']
        labels = list(dict.fromkeys(hist))
        label = edge['append_label']
        choices = [labels[label]] if label < len(labels) else [d for d in range(9) if d not in hist]
        # Entirely unused coordinates are interchangeable under a cube automorphism.
        fresh_used = False
        for d in choices:
            if d not in dirs:
                if fresh_used:
                    continue
                fresh_used = True
            y = path[-1] ^ (1 << d)
            if y in path or any((y ^ x).bit_count() == 1 for x in path[:-1]):
                continue
            rec(path + [y], dirs + [d], cs + [edge['count']])
            if stopped:
                return
    rec(path, initial, [])
    return {'status': stopped or 'EXHAUSTED', 'nodes': visits, 'seconds': time.monotonic()-start,
            'maximum_edges_if_exhausted': len(best[0])-1 if not stopped else None,
            'path': best[0], 'directions': best[1], 'counts_at_indices_7_onward': best[2],
            'limits': {'target_edges': target, 'seconds': seconds, 'nodes': nodes},
            'scope': 'Direction geometry only; counts have not yet been realized by a common selected set.'}


def solve_model(spec, logpath):
    from ortools.sat.python import cp_model
    import ortools
    n = spec.get('n', 9)
    N = 1 << n
    model = cp_model.CpModel()
    x = [model.new_bool_var(f'x{v}') for v in range(N)]
    end = [model.new_bool_var(f'end{v}') for v in range(N)]
    for v in range(N):
        model.add(end[v] <= x[v])
        model.add(sum(x[v ^ (1 << k)] for k in range(n)) == 2-end[v]).only_enforce_if(x[v])
    model.add(sum(end) == 2)
    model.add(sum(x) >= spec.get('min_vertices', 2))
    if 'vertices' in spec:
        model.add(sum(x) == spec['vertices'])
    # Dummy vertex 0 closes a selected induced path into one directed circuit.
    # Self-loops represent exactly the unselected vertices. Both orientations allowed.
    arcs = []
    for v in range(N):
        arcs.append((v+1, v+1, x[v].Not()))
        incoming = model.new_bool_var(f'start{v}')
        outgoing = model.new_bool_var(f'finish{v}')
        arcs.extend([(0, v+1, incoming), (v+1, 0, outgoing)])
        model.add(incoming + outgoing == end[v])
        for k in range(n):
            w = v ^ (1 << k)
            arc = model.new_bool_var(f'arc{v}_{w}')
            model.add(arc <= x[v])
            model.add(arc <= x[w])
            arcs.append((v+1, w+1, arc))
    model.add_circuit(arcs)
    for v in spec.get('selected', []):
        model.add(x[v] == 1)
    for v in spec.get('absent', []):
        model.add(x[v] == 0)
    if 'fixed_set' in spec:
        selected = set(spec['fixed_set'])
        for v in range(N):
            model.add(x[v] == int(v in selected))
    for c in spec.get('centres', []):
        v, a, b, lo, hi = c
        free = [1-x[v ^ (1 << i) ^ (1 << j)] for i, j in it.combinations(range(n), 2)
                if i not in (a, b) and j not in (a, b)]
        model.add(sum(free) >= lo)
        model.add(sum(free) <= hi)
    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.random_seed = 20261020
    solver.parameters.max_time_in_seconds = spec.get('seconds', 20)
    solver.parameters.max_memory_in_mb = 512
    solver.parameters.log_search_progress = True
    solver.parameters.log_to_stdout = False
    log = open(logpath, 'w', encoding='utf-8')
    solver.log_callback = lambda s: (log.write(s+'\n'), log.flush())
    status = solver.solve(model)
    log.write(solver.response_stats()+'\n')
    log.close()
    out = {'status': solver.status_name(status), 'solver': 'OR-Tools CP-SAT', 'version': ortools.__version__,
           'seed': 20261020, 'threads': 1, 'time_limit_seconds': spec.get('seconds',20),
           'memory_limit_mb': 512, 'wall_seconds': solver.wall_time,
           'model_sha256': hashlib.sha256(str(model.proto).encode()).hexdigest(),
           'response': solver.response_stats(),
           'scope': 'Exact selected-vertex induced-path model; solver outcomes are not Lean proofs.'}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sel = {v for v in range(N) if solver.value(x[v])}
        adj = {v: [v^(1<<k) for k in range(n) if v^(1<<k) in sel] for v in sel}
        endpoints = [v for v in sel if len(adj[v]) == 1]
        assert len(endpoints) == 2
        path = [min(endpoints)]
        while len(path) < len(sel):
            nxt = [w for w in adj[path[-1]] if len(path)<2 or w!=path[-2]]
            assert len(nxt) == 1
            path.append(nxt[0])
        out['witness'] = census(path, n, details=True)
        for v,a,b,lo,hi in spec.get('centres',[]):
            idx = path.index(v)
            assert 0 < idx < len(path)-1
            assert {path[idx-1]^v,path[idx+1]^v} == {1<<a,1<<b}
            assert lo <= out['witness']['alpha'][idx] <= hi
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', default='20261020-a')
    ap.add_argument('--group', choices=['controls','cycles','solver'], required=True)
    ap.add_argument('--source-run', default='20261020-a', help='Frozen cycle extraction to read for solver probes')
    args = ap.parse_args()
    run = HERE / 'runs' / args.run
    run.mkdir(parents=True, exist_ok=True)
    lock = run / 'RUNNING.lock'
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise SystemExit('Run lock exists. Inspect its PID before resuming; do not delete an active lock.')
    os.write(fd, json.dumps({'pid':os.getpid(),'start':now()}).encode())
    os.close(fd)
    current = subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
    def case(name, spec, fn):
        resultfile = run / (name+'.json')
        if resultfile.exists():
            saved = json.loads(resultfile.read_text(encoding='utf-8'))
            if saved['code_sha256'] != sha(__file__):
                raise RuntimeError('Code changed; choose a new run id instead of mixing provenance.')
            print('SAVED',name,flush=True)
            return saved['result']
        write(run / (name+'.input.json'), spec)
        write(run/'status.json', {'pid':os.getpid(),'running':True,'current':name,'updated':now(),
                                 'evidence':'计算检验；不是 Lean 定理'})
        start = time.monotonic()
        try:
            result = fn()
        except BaseException as e:
            write(run/(name+'.failure.json'),{'error':repr(e),'time':now(),'code_sha256':sha(__file__)})
            raise
        record = {'base_git':BASE,'run_git':current,'code_sha256':sha(__file__),
                  'input_sha256':sha(run/(name+'.input.json')),'python':platform.python_version(),
                  'started_by_pid':os.getpid(),'finished':now(),'elapsed_seconds':time.monotonic()-start,
                  'solver':'none unless specified in result','threads':1,'seed':None,'time_limit':None,
                  'result':result}
        write(resultfile,record)
        print(name, result.get('status','CHECKED'), 'seconds',round(record['elapsed_seconds'],2),flush=True)
        return result
    try:
        if args.group == 'controls':
            bankfile=ROOT/'work/bank9.json'
            case('bank131',{'input':str(bankfile.relative_to(ROOT)),'sha256':sha(bankfile)},
                 lambda:{'status':'CHECKED','cases':[census(e['vertex_sequence'],9) for e in json.loads(bankfile.read_text())]})
            for n in range(2,5):
                case(f'exhaustive_q{n}',{'n':n,'root':0},lambda n=n:exhaustive(n))
            case('sharp21',{'n':9,'construction':'homogeneous saturated shell'},
                 lambda:{'status':'COUNTEREXAMPLE','refutes':'All empty squares have at most 20 selected neighbours',
                         'witness':census(sharp_path(9),9,details=True)})
        elif args.group == 'cycles':
            cyc=case('cycle_extract',{'mean':'7/2','period_counts':[2,3,6,2,2,6]},extract_cycle)
            case('cycle_lift',{'cycle_sha256':sha(run/'cycle_extract.json'),'seconds':12,'nodes':200000},
                 lambda:lift_cycle(cyc))
        else:
            # Positive and negative controls for the full, connected global encoding.
            for n in [3,4]:
                p=sharp_path(n)
                spec={'n':n,'fixed_set':p,'seconds':5}
                case(f'model_q{n}_positive',spec,lambda spec=spec,n=n:solve_model(spec,run/f'model_q{n}_positive.log'))
            spec={'n':3,'fixed_set':[0,1,3,2],'seconds':5}
            case('model_cycle_negative',spec,lambda:solve_model(spec,run/'model_cycle_negative.log'))
            for mixed, minv in [(False,28),(True,40)]:
                selected=[]; absent=[0,1,2,3]
                for k in range(2,9):
                    miss=1 if mixed and k==2 else 0
                    selected += [q^(1<<k) for q in range(4) if q!=miss]
                    absent.append(miss^(1<<k))
                spec={'n':9,'selected':selected,'absent':absent,'min_vertices':minv,'seconds':30}
                name='mixed_shell40' if mixed else 'homogeneous_shell28'
                case(name,spec,lambda spec=spec,name=name:solve_model(spec,run/(name+'.log')))
            cyc=json.loads((HERE/'runs'/args.source_run/'cycle_extract.json').read_text())['result']
            ds=cyc['edges'][0]['shape'][:]
            counts=[]
            for t in range(10):
                edge=cyc['edges'][t % len(cyc['edges'])]
                assert list(canon(ds[-7:])) == edge['shape']
                labels=list(dict.fromkeys(ds[-7:]))
                assert edge['append_label'] < len(labels), 'This probe requires a deterministic cycle lift'
                ds.append(labels[edge['append_label']])
                counts.append(edge['count'])
            path=[0]
            for d in ds:
                path.append(path[-1] ^ (1<<d))
            for length in [1,2,3,4,5,6,8,10]:
                if length>len(counts):
                    continue
                centres=[[path[7+j],ds[6+j],ds[7+j],counts[j],counts[j] if counts[j]<6 else 21]
                         for j in range(length)]
                # Only the central block is required. Prior six edges in the lift are not fixed.
                spec={'n':9,'selected':path[6:8+length],'centres':centres,'seconds':20,
                      'description':'Shared global S, free outside vertices, exactly one induced path.'}
                name=f'joint_cycle_{length:02}'
                case(name,spec,lambda spec=spec,name=name:solve_model(spec,run/(name+'.log')))
        write(run/'status.json',{'pid':None,'running':False,'current':args.group+' finished','updated':now(),
                                 'evidence':'计算检验；不是 Lean 定理'})
    finally:
        lock.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
