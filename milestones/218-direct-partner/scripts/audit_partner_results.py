"""Read-only audit of saved partner records. Run only after the terminal notice.

Loads protobuf definitions directly; never imports the OR-Tools package
initializer, CP-SAT solver, NumPy, or Pandas. Does not execute a search.
"""
from pathlib import Path
from collections import Counter
import hashlib, importlib.util, json, sys

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
assert not (H / 'data/partner-search.lock').exists(), 'Wait for the parent terminal notice'
PACKAGE = R / 'work/solver_packages'
sys.path.insert(0, str(PACKAGE))
from google.protobuf import text_format
PROTO_SOURCE = PACKAGE / 'ortools/sat/cp_model_pb2.py'
spec = importlib.util.spec_from_file_location('audit_cp_model_pb2', PROTO_SOURCE)
proto = importlib.util.module_from_spec(spec)
spec.loader.exec_module(proto)
assert 'ortools' not in sys.modules and 'ortools.sat.python.cp_model' not in sys.modules

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def induced(path, width):
    assert len(path) == len(set(path)) and all(0 <= v < 2**width for v in path)
    assert all(((path[i] ^ path[j]).bit_count() == 1) == (j == i + 1)
               for i in range(len(path)) for j in range(i + 1, len(path)))

def components(vertices, neighbours):
    remaining, output = set(vertices), []
    while remaining:
        first = min(remaining); remaining.remove(first)
        found, pending = {first}, [first]
        while pending:
            v = pending.pop()
            for w in sorted(neighbours[v] & remaining):
                remaining.remove(w); found.add(w); pending.append(w)
        output.append(sorted(found))
    return output

def ordered_path(vertices, root, finish, neighbours):
    selected, output, previous = set(vertices), [root], None
    while output[-1] != finish:
        options = neighbours[output[-1]] & selected
        if previous is not None:
            options -= {previous}
        assert len(options) == 1
        nxt = next(iter(options)); assert nxt not in output
        previous = output[-1]; output.append(nxt)
    assert set(output) == selected
    induced(output, 8)
    return output

def validate_cycle(cycle, allowed, neighbours):
    assert len(cycle) == len(set(cycle)) >= 4 and set(cycle) <= allowed
    assert all(len(neighbours[v] & set(cycle)) == 2 for v in cycle)
    assert len(components(cycle, neighbours)) == 1

MIN_INT64 = -(2**63)
def model_signatures(root, vertices, neighbours, cycles):
    even = [v for v in vertices if v.bit_count() % 2 == 0]
    odd = [v for v in vertices if v.bit_count() % 2 == 1]
    names = ['x' + str(v) for v in vertices] + ['end' + str(v) for v in odd]
    index = {name: i for i, name in enumerate(names)}
    xv = {v: index['x' + str(v)] for v in vertices}
    ev = {v: index['end' + str(v)] for v in odd}
    result = []
    def add(coefficients, low, high, enforcement=()):
        result.append((tuple(enforcement), tuple(sorted(coefficients.items())), (low, high)))
    add({xv[root]: 1}, 1, 1)
    add({xv[v]: 1 for v in even}, 47, 47)
    add({xv[v]: 1 for v in odd}, 47, 47)
    add({ev[v]: 1 for v in odd}, 1, 1)
    for v in vertices:
        degree = {xv[w]: 1 for w in neighbours[v]}
        if v == root:
            add(degree, 1, 1)
        elif v in ev:
            add({ev[v]: 1, xv[v]: -1}, MIN_INT64, 0)
            add(degree | {ev[v]: 1}, 2, 2, (xv[v],))
        else:
            add(degree, 2, 2, (xv[v],))
    for c in cycles:
        add({xv[v]: 1 for v in c}, MIN_INT64, len(c) - 1)
    return names, result

def check_model(path, root, vertices, neighbours, cycles):
    m = proto.CpModelProto()
    text_format.Parse(path.read_text(encoding='utf-8'), m)
    assert {field.name for field, _ in m.ListFields()} <= {'variables', 'constraints'}
    names, expected = model_signatures(root, vertices, neighbours, cycles)
    assert len(m.variables) == len(names) == 237
    for v, name in zip(m.variables, names):
        assert v.name == name and list(v.domain) == [0, 1]
        assert {field.name for field, _ in v.ListFields()} <= {'name', 'domain'}
    actual = []
    for c in m.constraints:
        assert c.WhichOneof('constraint') == 'linear'
        assert {field.name for field, _ in c.ListFields()} <= {'enforcement_literal', 'linear'}
        assert len(c.linear.vars) == len(c.linear.coeffs)
        terms = Counter()
        for v, coefficient in zip(c.linear.vars, c.linear.coeffs):
            assert 0 <= v < len(names)
            terms[v] += coefficient
        terms = {v: coefficient for v, coefficient in terms.items() if coefficient}
        actual.append((tuple(c.enforcement_literal), tuple(sorted(terms.items())), tuple(c.linear.domain)))
    assert actual == expected, f'Model formula/order mismatch: {path}'
    return {'sha256': sha(path), 'variables': len(names), 'constraints': len(actual)}

def resource_record(folder, archived=False):
    record = read(folder / 'execution.json')
    assert record['status'] in ['ACCEPTED_NATIVE_RESULT', 'INTERRUPTED']
    for name, expected in record['pins'].items():
        path = folder / (Path(name).name + '.txt') if archived and name.startswith('scripts') else H / name
        assert sha(path) == expected, str(path)
    for name in ['stdout', 'stderr']:
        assert sha(folder / (name + '.log')) == record[name + '_sha256']
    gate = record['resource_gate']
    assert not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3
    samples = record['resource_samples']
    private = [x['private_bytes'] for x in samples if x['private_bytes'] is not None]
    if record['status'] == 'ACCEPTED_NATIVE_RESULT':
        assert record['exit_code'] == 0 and record['stop_reason'] is None
        assert all(not x['errors'] and not x['lean_processes'] and x['free_bytes'] >= 768*1024**2
                   and (x['private_bytes'] is None or x['private_bytes'] <= 256*1024**2) for x in samples)
    elif record['stop_reason'] == 'MEMORY_LIMIT':
        assert max(private) > 256*1024**2
    return record, {'execution_sha256': sha(folder / 'execution.json'), 'status': record['status'],
        'exit_code': record['exit_code'], 'stop_reason': record['stop_reason'],
        'wall_seconds': record['wall_seconds'], 'peak_private_bytes': max(private, default=None),
        'minimum_sample_free_bytes': min((x['free_bytes'] for x in samples), default=None)}

seed = read(H / 'data/seed98.json')['vertex_sequence']
assert len(seed) == 99 and seed[0] == 0 and seed[-1] == 78
induced(seed, 8)
saved_graph = read(H / 'data/complement-graph.json')
assert saved_graph['sha256'] == sha(H / 'data/seed98.json')
failed_folder = H / 'data/root-0'
failed, failed_review = resource_record(failed_folder, archived=True)
assert failed['status'] == 'INTERRUPTED' and failed['stop_reason'] == 'MEMORY_LIMIT'
assert not (failed_folder / 'result.json').exists() and not (failed_folder / 'initial-model.pbtxt').exists()
assert (failed_folder / 'stdout.log').read_bytes() == b'' and (failed_folder / 'stderr.log').read_bytes() == b''
batch = read(H / 'data/threads1/batch-progress.json')
reviews = []
thread_limits = {k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']}
for batch_row in batch['receipts']:
    root = batch_row['root']; assert root in [0, 78]
    folder = H / 'data/threads1' / ('root-' + str(root))
    execution, resources = resource_record(folder)
    assert batch_row == {'root': root, 'receipt_sha256': resources['execution_sha256'],
        'status': execution['status'], 'solver_status': execution.get('solver_status'),
        'stop_reason': execution['stop_reason']}
    assert execution['thread_environment'] == thread_limits
    cmd = execution['command']
    assert cmd[1:4] == ['-B','-X','utf8'] and Path(cmd[4]) == H / 'scripts/partner_search.py'
    assert cmd[5:8] == ['--root', str(root), '--seconds'] and float(cmd[8]) == 240.0
    assert cmd[9] == '--output-dir' and Path(cmd[10]).resolve() == folder.resolve()
    vertices = sorted(set(range(256)) - (set(seed) - {root}))
    allowed = set(vertices)
    neighbours = {v: {v ^ (1 << k) for k in range(8)} & allowed for v in vertices}
    graph = next(x for x in saved_graph['reports'] if x['root'] == root)
    assert graph['allowed_vertices'] == vertices and len(vertices) == 158
    even = [v for v in vertices if v.bit_count() % 2 == 0]
    odd = [v for v in vertices if v.bit_count() % 2 == 1]
    assert len(even) == len(odd) == 79 and root in even
    initial = graph['coordinate_squares'] + graph['three_cube_induced_six_cycles']
    assert len({tuple(sorted(c)) for c in initial}) == len(initial)
    for c in initial:
        validate_cycle(c, allowed, neighbours)
    assert all(len(c) == 4 for c in graph['coordinate_squares'])
    assert all(len(c) == 6 for c in graph['three_cube_induced_six_cycles'])
    current = {'root': root, 'resources': resources, 'allowed_vertices': len(vertices),
               'initial_cycle_cuts': len(initial), 'models': {}, 'verified_rooted_components': []}
    if (folder / 'initial-model.pbtxt').exists():
        current['models']['initial'] = check_model(folder / 'initial-model.pbtxt', root, vertices, neighbours, initial)
    if execution['status'] != 'ACCEPTED_NATIVE_RESULT':
        assert not (folder / 'checkpoint.json').exists(), 'Interrupted checkpoint requires explicit iteration review before acceptance'
        current['conclusion'] = 'INTERRUPTED_NO_EXCLUSION'
        reviews.append(current)
        continue
    result = read(folder / 'result.json')
    assert sha(folder / 'result.json') == execution['result_sha256']
    assert result['root'] == root and result['target_edges'] == 93 and result['target_q9_edges'] == 192
    assert result['status'] == execution['solver_status']
    assert result['status'] in ['FEASIBLE','UNKNOWN','INFEASIBLE','MODEL_INVALID']
    assert result['time_limit'] == 240.0 and 0 <= result['elapsed_seconds'] <= execution['wall_seconds']
    assert result['source_sha256'] == sha(H / 'scripts/partner_search.py')
    assert result['seed_sha256'] == sha(H / 'data/seed98.json')
    assert result['graph_sha256'] == sha(H / 'data/complement-graph.json')
    assert result['initial_model_sha256'] == current['models']['initial']['sha256']
    description = read(folder / 'model-description.json')
    for key in ['source_sha256','seed_sha256','graph_sha256','initial_model_sha256','ortools_version']:
        assert description[key] == result[key]
    assert description['root'] == root and description['vertices'] == vertices
    assert description['target_edges'] == 93 and description['selected_even'] == description['selected_odd'] == 47
    assert description['free_endpoints'] == odd
    assert description['initial_cycle_cuts'] == initial
    assert description['replacement_restrictions'] == description['symmetry_restrictions'] == []
    cuts, last_selected, final_path = [], None, None
    terminal_status, solver_seconds = None, 0.0
    for index, entry in enumerate(result['iterations']):
        assert entry['iteration'] == index
        assert entry['solver_seconds'] >= 0 and entry['branches'] >= 0 and entry['conflicts'] >= 0
        solver_seconds += entry['solver_seconds']
        status = entry['status']
        if status not in ['FEASIBLE','OPTIMAL']:
            assert index == len(result['iterations']) - 1 and status in ['UNKNOWN','INFEASIBLE','MODEL_INVALID']
            assert not any(k in entry for k in ['selected','components','endpoint','added_cycle_cuts'])
            terminal_status = status
            continue
        selected = entry['selected']; chosen = set(selected); finish = entry['endpoint']
        assert selected == sorted(chosen) and len(selected) == 94 and chosen <= allowed and root in chosen
        assert finish in chosen and finish in odd
        assert len(chosen & set(even)) == len(chosen & set(odd)) == 47
        assert all(len(neighbours[v] & chosen) == (1 if v in [root, finish] else 2) for v in chosen)
        assert all(not set(c) <= chosen for c in initial + cuts)
        parts = components(chosen, neighbours)
        assert parts == entry['components']
        path_part = next(c for c in parts if root in c)
        assert finish in path_part
        cycles = [c for c in parts if root not in c]
        assert cycles == entry['added_cycle_cuts']
        for c in cycles:
            validate_cycle(c, allowed, neighbours)
            assert c not in initial and c not in cuts
        q = ordered_path(path_part, root, finish, neighbours)
        assert set(seed) & set(q) == {root}
        oriented = seed if seed[-1] == root else list(reversed(seed))
        joined = oriented + [v + 256 for v in q]
        induced(joined, 9)
        current['verified_rooted_components'].append({'iteration': index, 'partner_edges': len(q)-1,
            'joined_q9_edges': len(joined)-1, 'partner': q,
            'scope': 'Validated complete target' if not cycles else 'Warm-start component only'})
        last_selected = selected
        if not cycles:
            assert index == len(result['iterations']) - 1 and len(q) == 94
            final_path = q
            assert result['partner'] == q and result['joined_q9'] == joined
        else:
            cuts.extend(cycles)
    assert result['dynamic_cycle_cuts'] == cuts and result['initial_cycle_cut_count'] == len(initial)
    assert result['last_relaxation_selection'] == last_selected
    if result['status'] == 'FEASIBLE':
        assert final_path is not None and terminal_status is None
    else:
        assert final_path is None and result['partner'] is None and result['joined_q9'] is None
        if terminal_status is not None:
            assert result['status'] == terminal_status
        else:
            assert result['status'] == 'UNKNOWN'
    current['models']['final'] = check_model(folder / 'final-model.pbtxt', root, vertices, neighbours, initial + cuts)
    assert result['final_model_sha256'] == current['models']['final']['sha256']
    current.update(status=result['status'], result_sha256=sha(folder / 'result.json'),
        model_description_sha256=sha(folder / 'model-description.json'), iterations=len(result['iterations']),
        feasible_relaxation_iterations=len(current['verified_rooted_components']), dynamic_cycle_cuts=len(cuts),
        solver_seconds=solver_seconds, elapsed_seconds=result['elapsed_seconds'],
        longest_partner_edges=max((x['partner_edges'] for x in current['verified_rooted_components']), default=None),
        conclusion=('VALIDATED_192_EDGE_CONSTRUCTION' if final_path is not None else
                    'NATIVE_FIXED_ROOT_INFEASIBLE_WITHOUT_REPLAY_CERTIFICATE' if result['status']=='INFEASIBLE' else
                    'MODEL_INVALID_NO_MATHEMATICAL_CONCLUSION' if result['status']=='MODEL_INVALID' else
                    'UNKNOWN_NO_EXCLUSION'))
    reviews.append(current)
assert len({x['root'] for x in reviews}) == len(reviews)
assert not (H / 'data/partner-search.lock').exists()
report = {'status':'PASS_SAVED_MODEL_AND_RECORD_AUDIT', 'first_failed_attempt': failed_review,
    'retry_roots': reviews, 'retry_solver_seconds': sum(x.get('solver_seconds',0) for x in reviews),
    'roots_without_terminal_receipts': sorted({0,78} - {x['root'] for x in reviews}),
    'retry_feasible_relaxations': sum(x.get('feasible_relaxation_iterations',0) for x in reviews),
    'retry_dynamic_cuts': sum(x.get('dynamic_cycle_cuts',0) for x in reviews),
    'pins': {name:sha(H/name) for name in ['scripts/audit_partner_results.py','scripts/partner_search.py',
        'scripts/run_partner.py','scripts/native_resources.py','data/seed98.json','data/complement-graph.json',
        'data/threads1/batch-progress.json','logs/partner-model-review.md']},
    'protobuf_definition_sha256':sha(PROTO_SOURCE),
    'scope':'No solver execution or proof replay. Exact exported linear model formula/order, native records and saved paths are inspected. First interrupted attempt excluded from retry counts. Native infeasibility has no separate certificate; UNKNOWN gives no exclusion.'}
(H/'data/partner-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k not in ['retry_roots','pins']},indent=2))
for row in reviews:
    print(json.dumps({k:v for k,v in row.items() if k!='verified_rooted_components'},indent=2))
