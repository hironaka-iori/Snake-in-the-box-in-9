"""One bounded test of a weaker share floor using a saved potential.

No optimization, solver, Lean process, or modification of inherited inputs.
The result concerns the pinned finite arrays and explicit conditional premises.
"""
from pathlib import Path
from fractions import Fraction
import datetime, gzip, hashlib, importlib.util, json, subprocess, sys, time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R / 'milestones/97-geometric-credit-integration/floor-sensitivity'
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def save(name, data):
    target = H / 'data' / name
    assert not target.exists(), 'Preserve the existing result'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8', newline='\n')

started = time.monotonic()
resources = subprocess.check_output(['powershell.exe', '-NoProfile', '-Command',
    '$o=Get-CimInstance Win32_OperatingSystem; @{free_bytes=([long]$o.FreePhysicalMemory*1024)} | ConvertTo-Json -Compress'], text=True)
resources = json.loads(resources)
assert resources['free_bytes'] >= 3 * 1024**3
spec = importlib.util.spec_from_file_location('saved_floor_inputs149', P / 'test.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
np = parent.np
meta, arrays, shapes, entering, full, cycle, paths, pins = parent.setup()
assert pins == read(P / 'input-pins.json')['files']
pins[(P/'test.py').relative_to(R).as_posix()] = sha(P/'test.py')
base = arrays['weight']
code = arrays['count_code']
weight16 = full.copy()
chosen034 = shapes == parent.SHAPES.index('012034')
weight16[chosen034] = np.maximum(base[chosen034], entering[chosen034] + 18)
floor18 = P / '012034-minimum/floor18.json'
saved = read(floor18)
assert hashlib.sha256(weight16.tobytes()).hexdigest() == saved['weight_sha256']
archive = floor18.parent / saved['potential_file']
raw = gzip.decompress(archive.read_bytes())
assert hashlib.sha256(raw).hexdigest() == saved['potential_sha256']
potential = np.frombuffer(raw, dtype='<i8')
assert len(potential) == meta['states'] and potential.min() == 0 and potential.max() == 602
u, v = arrays['U'], arrays['V']
slack = weight16 + potential[u] - potential[v] - 496
assert np.all(slack >= 0)

chosen032 = shapes == parent.SHAPES.index('012032')
a = code // 6**3 % 6 + 1
b = code // 6 % 6 + 1
event = chosen032 & (a < 6) & (b < 6) & (a+b <= 9)
weight15 = weight16.copy()
weight15[chosen032] = np.maximum(base[chosen032], entering[chosen032] + 15)
delta = weight16 - weight15
assert np.all((delta == 0) | (delta == 1))
candidate = weight15 + event.astype(np.int64)
candidate_slack = candidate + potential[u] - potential[v] - 496
violating = np.flatnonzero(candidate_slack < 0)
uncovered = np.flatnonzero((delta > 0) & ~event)
lost_tight = np.flatnonzero((delta > 0) & (slack == 0))

def rows(indices):
    result = []
    for i in indices:
        i = int(i)
        result.append(dict(edge=i, u=int(u[i]), v=int(v[i]),
            direction=int(arrays['direction'][i]), history=int(arrays['history'][i]),
            count_code=int(code[i]), counts=[int(code[i]//6**j%6+1) for j in range(5,-1,-1)],
            shape=parent.SHAPES[int(shapes[i])], base_weight=int(base[i]),
            original_weight=int(weight16[i]), weaker_weight=int(weight15[i]),
            event=bool(event[i]), original_slack=int(slack[i]), candidate_slack=int(candidate_slack[i])))
    return result

# Re-evaluate the saved obstruction on the same floor18 and floor15 weights.
old_obstruction = P / 'case7301.json'
walk = [x['edge'] for x in read(old_obstruction)['walk']]
parent.valid_walk(walk, arrays)
parent.valid_walk(cycle, arrays, True)
assert sum(int(candidate[i]) for i in cycle) == 1488 and not event[cycle].any()
length = len(walk)
walk_base_total = sum(int(weight15[i]) for i in walk)
walk_events = sum(bool(event[i]) for i in walk)
deficit0 = 496*length-walk_base_total
deficit1 = deficit0-walk_events
assert length <= 227

for path in [floor18, archive, old_obstruction,
             R/'milestones/144-countfree-share18/scripts/evaluate_graph.py']:
    pins[path.relative_to(R).as_posix()] = sha(path)
assert all(sha(R/p) == d for p,d in pins.items())
candidate_bound = Fraction(1098960+8*496+24+602, 4200+496)
assert candidate_bound == 235-Fraction(6,4696)
out = dict(status='PASS_SAVED_POTENTIAL' if not len(violating) else 'SAVED_POTENTIAL_REJECTS_WEAKER_FLOOR',
    timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    question='Can floor012032=15 plus occurrence credit1 retain the saved floor18 potential?',
    edge_count=len(u), state_count=meta['states'],
    fixed_floors=dict(zip(parent.SHAPES,[16,15,18,16,16,12,16,16,16])),
    event_rule='Suffix012032; second and fourth internal symbols both below6 and sum at most9.',
    occurrence_boundary_allowance_assumed=24, credit=1, mean=496, potential_range=602,
    original_potential_all_edges_pass=True, original_weight_sha256=saved['weight_sha256'],
    candidate_weight_sha256=hashlib.sha256(candidate.tobytes()).hexdigest(),
    changed_edges=int(np.count_nonzero(delta)),
    changed_edges_without_event=len(uncovered), changed_zero_slack_edges=len(lost_tight),
    violated_edges=len(violating), first_violations=rows(violating[:12]),
    would_be_comparison_if_potential_valid=str(candidate_bound),
    saved_walk=dict(length=length, weight_without_credit=walk_base_total,
        occurrence_events=walk_events, deficit_without_credit=deficit0, deficit_credit1=deficit1,
        obstruction_credit1=deficit1+24 >= 632,
        edge_ids=walk, cycle_ids=cycle,
        general_obstruction=f'{deficit0} + ({24-walk_events}) C >= 632'),
    source_files_sha256=pins, script_sha256=sha(Path(__file__)),
    resource_preflight=resources, seconds=time.monotonic()-started,
    scope='Exact finite-array comparison only. No new potential search or local share proof. A rejected saved potential does not rule out a different potential. Any global234 consequence also requires the reference, graph coverage, share, occurrence and interpretation premises.')
save('saved-potential-test.json', out)
print(json.dumps({k:out[k] for k in ['status','edge_count','changed_edges','changed_edges_without_event','violated_edges','saved_walk','seconds']}), flush=True)
