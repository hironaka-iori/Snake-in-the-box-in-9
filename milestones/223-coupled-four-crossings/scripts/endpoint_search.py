"""Search both Q8 faces jointly, with exactly four crossings and free ports."""
from pathlib import Path
import argparse, hashlib, json, sys, time
H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sys.path.insert(0, str(R / 'work/solver_packages'))
from ortools.sat.python import cp_model

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p, x): p.write_text(json.dumps(x, indent=2) + '\n', encoding='utf-8')

ap = argparse.ArgumentParser()
ap.add_argument('--index', type=int, default=0)
ap.add_argument('--omissions', type=int, default=4)
ap.add_argument('--seconds', type=float, default=90)
ap.add_argument('--tag', required=True)
ap.add_argument('--endpoint', type=int, required=True)
a = ap.parse_args()
dest = H / 'data' / (a.tag + '.json')
assert not dest.exists()
source = R / 'milestones/195-shortened-reroutings/data/forest-profiles.json'
profile = json.loads(source.read_bytes())['bank_forests'][a.index]
blocks = [profile['complement_paths'][0], profile['paths'][0],
          profile['complement_paths'][1], profile['paths'][1],
          profile['complement_paths'][2]]
seed = [v + 256 * (i % 2) for i, block in enumerate(blocks) for v in block]
assert len(seed) == len(set(seed)) == 192 and seed[0] == 0
assert all(((u ^ seed[j]).bit_count() == 1) == (j == i+1)
           for i, u in enumerate(seed) for j in range(i+1, len(seed)))
S = set(seed)
N = {v: [v ^ (1 << k) for k in range(9)] for v in range(512)}
m = cp_model.CpModel()
x = [m.new_bool_var('x' + str(v)) for v in range(512)]
end = [m.new_bool_var('end' + str(v)) for v in range(512)]
cross = [m.new_bool_var('cross' + str(v)) for v in range(256)]
for v in range(512):
    m.add(end[v] <= x[v])
    m.add(sum(x[w] for w in N[v]) == 2-end[v]).only_enforce_if(x[v])
    # With four crossings both endpoints are in the starting face. Root 0
    # and an even total length require both endpoints to have even parity.
    if v >= 256 or v.bit_count() % 2:
        m.add(end[v] == 0)
    m.add_hint(x[v], int(v in S))
assert a.endpoint < 256 and a.endpoint.bit_count() % 2 == 0
assert (a.endpoint ^ seed[-1]).bit_count() == 1 and a.endpoint not in S
m.add(end[a.endpoint] == 1)
m.add(x[seed[-1]] == 1)
m.add(end[0] == 1)
m.add(sum(end) == 2)
m.add(sum(x) == 193)
m.add(sum(x[v] for v in range(512) if v.bit_count() % 2 == 0) == 97)
for v in range(256):
    m.add(cross[v] <= x[v])
    m.add(cross[v] <= x[v+256])
    m.add(cross[v] >= x[v]+x[v+256]-1)
m.add(sum(cross) == 4)
m.add(sum(1-x[v] for v in seed) <= a.omissions)
# Require genuine coordinated changes, while keeping all joining ports free.
for face in range(2):
    m.add(sum(1-x[v] for v in seed if v // 256 == face) >= 1)
square_count = 0
for v in range(512):
    for i in range(9):
        for j in range(i+1, 9):
            sq = [v, v^(1<<i), v^(1<<j), v^(1<<i)^(1<<j)]
            if v == min(sq):
                m.add(sum(x[w] for w in sq) <= 3)
                square_count += 1
model = H / 'data' / (a.tag + '.pbtxt')
m.export_to_file(str(model))
record = dict(status='RUNNING', arguments=vars(a), seed=seed,
    source_sha256=sha(source), script_sha256=sha(__file__), model_sha256=sha(model),
    seed_index=profile['seed'], seed_coordinate=profile['coordinate'],
    seed_component_edges=[len(b)-1 for b in blocks], square_cuts=square_count,
    iterations=[], cycle_cuts=[], witness=None,
    scope='Root 0 fixed; other endpoint free. Exactly 193 vertices and four bit-8 crossings. '
          'At most the specified seed omissions, with at least one omission in each face. '
          'All ports variable. The old terminal vertex is retained internally and its specified neighbour is the new endpoint. Native feasibility search; no Lean infeasibility certificate.')
save(dest, record)
started = time.monotonic()
while True:
    remaining = a.seconds-(time.monotonic()-started)
    if remaining <= 0:
        record['status'] = 'TIME_LIMIT'
        break
    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.max_time_in_seconds = remaining
    solver.parameters.max_memory_in_mb = 256
    status = solver.solve(m)
    item = dict(status=solver.status_name(status), seconds=solver.wall_time,
                branches=solver.num_branches, conflicts=solver.num_conflicts)
    record['iterations'].append(item)
    if status not in [cp_model.FEASIBLE, cp_model.OPTIMAL]:
        record['status'] = solver.status_name(status)
        break
    selected = {v for v in range(512) if solver.value(x[v])}
    adj = {v: [w for w in N[v] if w in selected] for v in selected}
    pending = set(selected)
    components = []
    while pending:
        stack = [min(pending)]; component = set()
        while stack:
            v = stack.pop()
            if v in component: continue
            component.add(v); pending.remove(v)
            stack.extend(w for w in adj[v] if w not in component)
        components.append(component)
    cycles = [sorted(c) for c in components if all(len(adj[v]) == 2 for v in c)]
    item['component_sizes'] = sorted(map(len, components))
    item['new_cycles'] = len(cycles)
    if not cycles:
        assert len(components) == 1
        path = [0]
        while True:
            nxt = [w for w in adj[path[-1]] if len(path) == 1 or w != path[-2]]
            if not nxt: break
            assert len(nxt) == 1
            path.append(nxt[0])
            assert len(path) <= len(selected)
        assert len(path) == len(set(path)) == 193
        assert all(((u ^ path[j]).bit_count() == 1) == (j == i+1)
                   for i, u in enumerate(path) for j in range(i+1, len(path)))
        record['witness'] = dict(path=path, omitted=sorted(S-selected), added=sorted(selected-S))
        record['status'] = 'WITNESS'
        break
    for c in cycles:
        m.add(sum(x[v] for v in c) <= len(c)-1)
        record['cycle_cuts'].append(c)
    save(dest, record)
record['seconds'] = time.monotonic()-started
save(dest, record)
print(json.dumps({k: record[k] for k in ['status','seconds','iterations','witness']}), flush=True)
