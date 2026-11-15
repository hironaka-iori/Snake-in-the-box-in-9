"""Independent saved integer-row and rational-certificate audit; no solver imports."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import math

H = Path(__file__).resolve().parents[1]
def read(p): return json.loads(Path(p).read_bytes())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q): return [q.numerator, q.denominator]
def fraction(v):
    assert len(v) == 2 and all(type(t) is int for t in v) and v[1] > 0
    return Fraction(*v)

def intended(root, form, seed, graph):
    vertices = [v for v in range(256) if v not in seed or v == root]
    neighbours = {v: [w for w in vertices if (v ^ w).bit_count() == 1] for v in vertices}
    edges = [[v, w] for v in vertices for w in neighbours[v] if v < w]
    odd = [v for v in vertices if v.bit_count() % 2]
    assert len(vertices) == 158 and len(odd) == 79 and len(edges) == 337
    assert graph['allowed_vertices'] == vertices
    cycles = graph['coordinate_squares'] + graph['three_cube_induced_six_cycles']
    assert len({tuple(sorted(c)) for c in cycles}) == len(cycles)
    for c in cycles:
        assert len(c) in (4, 6) and len(set(c)) == len(c) and set(c) <= set(vertices)
        assert all(sum(w in neighbours[v] for w in c) == 2 for v in c)
        reached = {c[0]}
        while True:
            more = reached | {w for v in reached for w in c if w in neighbours[v]}
            if reached == more: break
            reached = more
        assert reached == set(c)
    names = [f'x{v}' for v in vertices] + [f'e{v}' for v in odd]
    xi = {v: names.index(f'x{v}') for v in vertices}
    ei = {v: names.index(f'e{v}') for v in odd}
    yi = {}
    if form == 'edge':
        for v, w in edges:
            yi[v, w] = len(names)
            names.append(f'y{v}_{w}')
    rows = []
    def add(name, terms, sense, rhs):
        d = {}
        for i, a in terms: d[i] = d.get(i, 0) + a
        rows.append(dict(name=name, terms=[[i, a] for i, a in sorted(d.items()) if a], sense=sense, rhs=rhs))
    add('root_selected', [(xi[root], 1)], 'eq', 1)
    add('root_degree', [(xi[v], 1) for v in neighbours[root]], 'eq', 1)
    add('one_free_endpoint', [(ei[v], 1) for v in odd], 'eq', 1)
    add('parity_balance', [(xi[v], -1 if v in odd else 1) for v in vertices], 'eq', 0)
    for v in vertices:
        if v in ei: add(f'endpoint_selected_{v}', [(ei[v], 1), (xi[v], -1)], 'le', 0)
        if v == root: continue
        ep = [(ei[v], 1)] if v in ei else []
        add(f'degree_lower_{v}', [(xi[v], 2)] + [(xi[w], -1) for w in neighbours[v]] + [(i, -a) for i, a in ep], 'le', 0)
        add(f'degree_upper_{v}', [(xi[v], len(neighbours[v])-2)] + [(xi[w], 1) for w in neighbours[v]] + ep, 'le', len(neighbours[v]))
    for i, c in enumerate(cycles): add(f'cycle_{i}', [(xi[v], 1) for v in c], 'le', len(c)-1)
    if form == 'edge':
        for u, v in edges:
            y = yi[u, v]
            add(f'edge_le_left_{u}_{v}', [(y, 1), (xi[u], -1)], 'le', 0)
            add(f'edge_le_right_{u}_{v}', [(y, 1), (xi[v], -1)], 'le', 0)
            add(f'edge_ge_both_{u}_{v}', [(xi[u], 1), (xi[v], 1), (y, -1)], 'le', 1)
        for v in vertices:
            terms = [(yi[min(v, w), max(v, w)], 1) for w in neighbours[v]]
            if v == root: add('edge_root_degree', terms, 'eq', 1)
            else: add(f'edge_degree_{v}', terms + [(xi[v], -2)] + ([(ei[v], 1)] if v in ei else []), 'eq', 0)
    return dict(root=root, form=form, variables=names, lower=[0]*len(names), upper=[1]*len(names),
                objective=[int(i < len(vertices)) for i in range(len(names))], rows=rows,
                vertices=vertices, edges=edges, cycles=cycles)

def certificate(model, cert):
    scale, weights = cert['scale'], cert['weights']
    assert type(scale) is int and scale > 0 and len(weights) == len(model['rows'])
    residual = [scale*c for c in model['objective']]
    rhs = 0
    for row, w in zip(model['rows'], weights):
        assert type(w) is int and (row['sense'] == 'eq' or w >= 0)
        assert row['sense'] in ('eq', 'le')
        rhs += w*row['rhs']
        for i, a in row['terms']: residual[i] -= w*a
    positive = [max(r, 0) for r in residual]
    numerator = rhs + sum(positive)
    upper = Fraction(numerator, scale)
    assert cert['residual'] == residual and cert['positive_residual'] == positive
    assert cert['upper_numerator'] == numerator and fraction(cert['upper_bound']) == upper
    return upper, sum(positive)

assert not (H/'data/lp-search.lock').exists()
execution = read(H/'data/lp-execution.json')
assert execution['status'] == 'ACCEPTED_NATIVE_RESULT' and execution['exit_code'] == 0 and execution['stop_reason'] is None
for p, h in execution['pins'].items(): assert sha(H/p) == h
for stream in ('stdout', 'stderr'): assert sha(H/f'logs/lp-{stream}.log') == execution[f'{stream}_sha256']
assert sha(H/'data/lp-summary.json') == execution['summary_sha256']
assert execution['thread_environment'] == {k: '1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
gate = execution['resource_gate']
assert not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3
for s in execution['resource_samples']:
    assert not s['errors'] and not s['lean_processes'] and s['free_bytes'] >= 768*1024**2
    assert s['private_bytes'] is None or s['private_bytes'] <= 256*1024**2
seed = read(H/'data/seed98.json')['vertex_sequence']
assert len(seed) == len(set(seed)) == 99 and seed[0] == 0 and seed[-1] == 78
assert all(0 <= v < 256 for v in seed)
for i, v in enumerate(seed):
    for j in range(i+1, len(seed)):
        assert ((v ^ seed[j]).bit_count() == 1) == (j == i+1)
graphs = read(H/'data/complement-graph.json')
assert graphs['sha256'] == sha(H/'data/seed98.json')
summary = read(H/'data/lp-summary.json')
assert [(s['root'], s['form']) for s in summary] == [(0,'vertex'),(0,'edge'),(78,'vertex'),(78,'edge')]
results, models = [], {}
for s in summary:
    root, form = s['root'], s['form']
    folder = H/'data'/f'{form}-{root}'
    model = read(folder/'model.json'); models[root, form] = model
    expected = intended(root, form, seed, next(g for g in graphs['reports'] if g['root'] == root))
    for key, value in expected.items(): assert model[key] == value, (root, form, key)
    assert model['source_sha256'] == sha(H/'scripts/linear_partner.py')
    assert model['seed_sha256'] == sha(H/'data/seed98.json') and model['graph_sha256'] == sha(H/'data/complement-graph.json')
    native, cert = read(folder/'native-result.json'), read(folder/'upper-certificate.json')
    assert native['status'] == 'OPTIMAL_NATIVE' and native['root'] == root and native['form'] == form
    assert native['model_sha256'] == cert['model_sha256'] == sha(folder/'model.json')
    assert len(native['values']) == len(model['variables']) and len(native['duals']) == len(model['rows'])
    assert all(math.isfinite(v) for v in native['values'] + native['duals'])
    upper, residual = certificate(model, cert)
    assert cert['scale'] == 10**6
    assert cert['weights'] == [max(0, round(w*cert['scale'])) if row['sense'] == 'le' else round(w*cert['scale']) for row, w in zip(model['rows'], native['duals'])]
    assert fraction(native['exact_upper']) == upper
    primal_path = folder/'primal-certificate.json'
    assert primal_path.exists() == native['exact_primal_reconstruction']
    primal = None; nonintegral = None
    if primal_path.exists():
        p = read(primal_path)
        assert p['model_sha256'] == sha(folder/'model.json')
        values = [fraction(v) for v in p['values']]
        assert len(values) == len(model['variables']) and all(0 <= v <= 1 for v in values)
        for row in model['rows']:
            lhs = sum((a*values[i] for i, a in row['terms']), Fraction())
            assert (lhs == row['rhs'] if row['sense'] == 'eq' else lhs <= row['rhs'])
        primal = sum((a*v for a, v in zip(model['objective'], values)), Fraction())
        assert primal == fraction(p['objective']) == fraction(native['exact_primal_objective']) and primal <= upper
        nonintegral = sum(v.denominator != 1 for v in values)
    expected_summary = {k: v for k, v in native.items() if k not in ('values','duals')}
    expected_summary.update(variables=len(model['variables']), constraints=len(model['rows']), upper_below_94=upper < 94)
    assert s == expected_summary
    pins = {p.name: sha(p) for p in folder.iterdir() if p.is_file()}
    results.append(dict(root=root, form=form, variables=len(model['variables']), rows=len(model['rows']), vertices=158,
        edges=337, cycles=len(model['cycles']), native_objective_not_exact_optimality=native['objective'],
        exact_upper=rat(upper), upper_below_94=upper < 94, exact_primal=rat(primal) if primal is not None else None,
        exact_primal_at_least_94=primal >= 94 if primal is not None else None,
        nonintegral_primal_coordinates=nonintegral, positive_residual_total=residual, source_pins=pins))
cycle_results = []
if (H/'data/cycle-summary.json').exists():
    ex = read(H/'data/cycles-execution.json')
    assert ex['status'] == 'ACCEPTED_NATIVE_RESULT' and ex['exit_code'] == 0 and ex['stop_reason'] is None
    for p, h in ex['pins'].items(): assert sha(H/p) == h
    for root in (0, 78):
        f = H/'data'/f'cycles-{root}'
        m, c, n = read(f/'model.json'), read(f/'upper-certificate.json'), read(f/'native-result.json')
        for key in ('variables','lower','upper','objective','rows','vertices','edges','cycles'):
            assert m[key] == models[root, 'edge'][key], (root, key)
        assert n['added_cycle_count'] == 0 and n['no_new_violations_at_tolerance'] is True
        assert n['model_sha256'] == c['model_sha256'] == sha(f/'model.json')
        bound, residual = certificate(m, c)
        assert rat(bound) == n['exact_upper']
        cycle_results.append(dict(root=root, unchanged_rows=True, added_cycle_count=0, exact_upper=rat(bound),
            absence_of_violated_cycles='Numerical tolerance observation only; exhaustive exact separation not checked.',
            source_pins={p.name: sha(p) for p in f.iterdir() if p.is_file()}))
report = dict(status='PASS_EXACT_SAVED_ROWS_AND_RATIONAL_UPPER_CERTIFICATES',
    scope='Independent reconstruction of every saved integer model row and exact residual upper certificates. No solver, compiler, search, or software tests. Numerical optimum claims are not certified.',
    models=results, cycle_models=cycle_results,
    resource=dict(seconds=execution['seconds'], peak_private_bytes=max(s['private_bytes'] or 0 for s in execution['resource_samples']),
                  minimum_free_bytes=min(s['free_bytes'] for s in execution['resource_samples']), stop_reason=execution['stop_reason']),
    pins={str(p.relative_to(H)): sha(p) for p in [Path(__file__),H/'scripts/linear_partner.py',H/'scripts/run_lp.py',H/'data/seed98.json',H/'data/complement-graph.json',H/'data/lp-summary.json',H/'data/lp-execution.json']})
assert not (H/'data/lp-search.lock').exists()
assert sha(H/'data/lp-summary.json') == execution['summary_sha256']
(H/'data/linear-audit.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(json.dumps(report, indent=2))
