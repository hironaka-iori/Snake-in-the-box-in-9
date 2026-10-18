"""Constructive search in the alternating 18-vertex cell family.

Direct degree constraints implement the table conditions without expanding
sixteen 4,973-row tables. Saved solutions are checked against those tables.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
TABLE = ROOT/'milestones/16-cycle-reservoirs/data/cell-states.json'
sys.path.insert(0, str(ROOT/'work'))
sys.path.insert(0, str(ROOT/'milestones/14-component-construction/scripts'))
from exact_search import cp_model
from component_search import components


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def local_cycles(table):
    cycles = set()
    for row in table['rows']:
        selected = [v for i,v in enumerate(table['vertices']) if row[0] >> i & 1]
        parts, adj = components(selected, 5)
        for part in parts:
            if all(len(adj[v]) == 2 for v in part):
                cycles.add(tuple(part))
    return sorted(cycles)


def inspect(selected, data):
    selected = set(selected)
    masks = []
    for h in range(16):
        table = data['tables'][h.bit_count()%2]
        mask = sum(1 << i for i,v in enumerate(table['vertices']) if (h*32+v) in selected)
        assert mask in {r[0] for r in table['rows']}
        masks.append(mask)
    parts, adj = components(selected, 9)
    assert all(len(adj[v]) in (1,2) for v in selected)
    assert sum(len(adj[v]) == 1 for v in selected) == 2
    paths = [c for c in parts if any(len(adj[v]) == 1 for v in c)]
    assert len(paths) == 1
    path = [min(v for v in paths[0] if len(adj[v]) == 1)]
    while True:
        nxt = [v for v in adj[path[-1]] if len(path) == 1 or v != path[-2]]
        if not nxt: break
        assert len(nxt) == 1 and nxt[0] not in path
        path.append(nxt[0])
    return {'seed_vertices':sorted(selected), 'cell_masks':masks, 'components':parts,
            'path_vertices':path, 'path_edges':len(path)-1,
            'cycle_lengths':sorted(len(c) for c in parts if c != paths[0])}


def run(args):
    data = json.loads(TABLE.read_text())
    cells = [[h*32+v for v in data['tables'][h.bit_count()%2]['vertices']] for h in range(16)]
    vertices = sorted(v for cell in cells for v in cell)
    allowed = set(vertices)
    m = cp_model.CpModel()
    x = {v:m.new_bool_var(f'x{v}') for v in vertices}
    end = {v:m.new_bool_var(f'e{v}') for v in vertices}
    m.add(sum(x.values()) == args.edges+1)
    m.add(sum(end.values()) == 2)
    for v in vertices:
        m.add(end[v] <= x[v])
        ns = [v^(1<<k) for k in range(9) if v^(1<<k) in allowed]
        m.add(sum(x[w] for w in ns) == 2-end[v]).only_enforce_if(x[v])
    local = [local_cycles(t) for t in data['tables']]
    initial_cuts = []
    if not args.allow_local_cycles:
        for h in range(16):
            for cycle in local[h.bit_count()%2]:
                cut = [h*32+v for v in cycle]
                m.add(sum(x[v] for v in cut) <= len(cut)-1)
                initial_cuts.append(cut)
    if args.connected:
        # One dummy joins the two endpoints; every selected graph edge must
        # belong to the circuit, since selected graph degrees are already 1/2.
        dummy = 512
        arcs = [(v,v,x[v].Not()) for v in vertices]
        for v in vertices:
            a,b = m.new_bool_var(f's{v}'),m.new_bool_var(f't{v}')
            arcs += [(dummy,v,a),(v,dummy,b)]
            m.add(a+b == end[v])
            for k in range(9):
                w = v^(1<<k)
                if w in x:
                    a = m.new_bool_var(f'a{v}_{w}')
                    m.add(a <= x[v]); m.add(a <= x[w])
                    arcs.append((v,w,a))
        m.add_circuit(arcs)
    hint = None
    if args.hint:
        hint = set(json.loads(args.hint.read_text())['seed_vertices'])
        assert hint <= allowed
        for v in vertices:
            if args.control: m.add(x[v] == int(v in hint))
            else: m.add_hint(x[v],int(v in hint))
    report = {'target_edges':args.edges, 'allowed_vertices':vertices,
              'connected_model':args.connected, 'control':args.control,
              'allow_local_cycles':args.allow_local_cycles,
              'initial_cycles':initial_cuts,'local_cycle_types':local,
              'table_sha256_lf':digest(TABLE),'script_sha256_lf':digest(Path(__file__)),
              'seed':args.seed,'workers':args.workers,'time_limit':args.seconds,
              'hint':str(args.hint) if args.hint else None,
              'scope':'Restricted alternating-cell family; UNKNOWN is unresolved, and INFEASIBLE is not a bound for Q9.',
              'rounds':[],'cuts_added':[]}
    start = time.monotonic()
    for iteration in range(args.rounds):
        remaining = args.seconds-(time.monotonic()-start)
        if remaining <= 0: break
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = remaining
        solver.parameters.num_search_workers = args.workers
        solver.parameters.random_seed = args.seed+iteration
        status = solver.solve(m)
        record = {'iteration':iteration,'status':solver.status_name(status),
                  'seconds':solver.wall_time,'branches':solver.num_branches,'conflicts':solver.num_conflicts}
        if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
            selected = [v for v in vertices if solver.value(x[v])]
            assert len(selected) == args.edges+1
            record.update(inspect(selected,data))
        report['rounds'].append(record)
        print(json.dumps({k:record[k] for k in ('iteration','status','seconds','path_edges','cycle_lengths') if k in record}),flush=True)
        if 'seed_vertices' not in record: break
        if len(record['components']) == 1:
            report['snake_vertices'] = record['path_vertices']; break
        if args.control: break
        m.clear_hints()
        for v in vertices: m.add_hint(x[v],int(v in record['seed_vertices']))
        for part in record['components']:
            if part == sorted(record['path_vertices']): continue
            m.add(sum(x[v] for v in part) <= len(part)-1)
            report['cuts_added'].append(part)
    report['elapsed_seconds'] = time.monotonic()-start
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--edges',type=int,default=196)
    p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--seed',type=int,default=196)
    p.add_argument('--rounds',type=int,default=20)
    p.add_argument('--connected',action='store_true')
    p.add_argument('--allow-local-cycles',action='store_true')
    p.add_argument('--control',action='store_true')
    p.add_argument('--hint',type=Path)
    p.add_argument('--output',type=Path,required=True)
    run(p.parse_args())
