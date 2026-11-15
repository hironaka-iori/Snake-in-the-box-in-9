"""Read-only exact audit of saved rational points and all-cycle potentials."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json

H = Path(__file__).resolve().parents[1]
def read(p): return json.loads(Path(p).read_bytes())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q): return [q.numerator, q.denominator]
def fraction(p):
    assert len(p) == 2 and all(type(v) is int for v in p) and p[1] > 0
    q = Q(*p)
    assert rat(q) == p
    return q

baseline_hash = 'b408c13775470f5bf903db4bdd52aa5d3444b0d7268847ff728018eaf5e11d37'
assert sha(H/'data/linear-audit.json') == baseline_hash
baseline = read(H/'data/linear-audit.json')
assert baseline['status'] == 'PASS_EXACT_SAVED_ROWS_AND_RATIONAL_UPPER_CERTIFICATES'
for p, h in baseline['pins'].items(): assert sha(H/p) == h
assert not (H/'data/lp-search.lock').exists()
execution = read(H/'data/rational-execution.json')
assert execution['status'] == 'ACCEPTED_NATIVE_RESULT' and execution['exit_code'] == 0 and execution['stop_reason'] is None
for p, h in execution['pins'].items(): assert sha(H/p) == h
for stream in ('stdout','stderr'):
    assert sha(H/f'logs/rational-{stream}.log') == execution[f'{stream}_sha256']
assert sha(H/'data/rational-summary.json') == execution['summary_sha256']
summary = read(H/'data/rational-summary.json')
assert [s['root'] for s in summary] == [0,78]
assert execution['thread_environment'] == {k:'1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
gate = execution['resource_gate']
assert not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3
for s in execution['resource_samples']:
    assert not s['errors'] and not s['lean_processes'] and s['free_bytes'] >= 768*1024**2
    assert s['private_bytes'] is None or s['private_bytes'] <= 256*1024**2
reports = []
for s in summary:
    root = s['root']; folder = H/'data'/f'rational-{root}'
    model_file = H/'data'/f'edge-{root}'/'model.json'
    model = read(model_file); cert = read(folder/'primal-certificate.json')
    prior = next(r for r in baseline['models'] if r['root'] == root and r['form'] == 'edge')
    assert sha(model_file) == prior['source_pins']['model.json'] == cert['model_sha256']
    assert sha(H/'scripts/rational_basis.py') == cert['source_sha256']
    assert sha(folder/'primal-certificate.json') == s['certificate_sha256']
    values = [fraction(v) for v in cert['values']]
    assert len(values) == len(model['variables']) == 574
    assert model['lower'] == [0]*574 and model['upper'] == [1]*574
    assert all(0 <= v <= 1 for v in values)
    tight = 0
    for row in model['rows']:
        lhs = sum((a*values[i] for i,a in row['terms']), Q())
        assert row['sense'] in ('le','eq')
        assert (lhs == row['rhs'] if row['sense'] == 'eq' else lhs <= row['rhs']), row['name']
        tight += lhs == row['rhs']
    objective = sum((a*v for a,v in zip(model['objective'], values)), Q())
    assert objective == fraction(cert['objective']) == fraction(s['objective']) and objective > 94
    assert float(objective) == s['objective_float']
    vertices, edges = model['vertices'], model['edges']
    assert len(vertices) == 158 and len(edges) == 337 and len(set(vertices)) == 158
    index = {v: i for i,v in enumerate(vertices)}
    assert model['variables'][:158] == [f'x{v}' for v in vertices]
    assert model['objective'] == [1]*158 + [0]*(574-158)
    costs = {v: 1-values[index[v]] for v in vertices}
    neighbours = {v: set() for v in vertices}
    for u,v in edges:
        assert u < v and (u ^ v).bit_count() == 1
        neighbours[u].add(v); neighbours[v].add(u)
    potentials = cert['potentials']
    assert [p['edge'] for p in potentials] == edges
    bounds = []; inequality_count = 0
    for stored in potentials:
        source,target = stored['edge']
        p = [fraction(q) for q in stored['distance']]
        assert len(p) == len(vertices) and p[index[source]] == 0
        deleted = (source,target)
        reached = {source}; todo = [source]
        while todo:
            u = todo.pop()
            for v in neighbours[u]:
                if (min(u,v),max(u,v)) == deleted or v in reached: continue
                reached.add(v); todo.append(v)
        assert target in reached and stored['target_reachable'] is True
        for u,v in edges:
            if (u,v) == deleted: continue
            assert abs(p[index[u]]-p[index[v]]) <= costs[u]+costs[v]
            inequality_count += 1
        twice_bound = p[index[target]]+costs[source]+costs[target]
        assert twice_bound >= 2
        bound = twice_bound/2
        assert bound == fraction(stored['cycle_lower_bound'])
        bounds.append(bound)
    assert inequality_count == 337*336
    assert min(bounds) == fraction(cert['minimum_cycle_cost']) == fraction(s['minimum_cycle_cost']) == 1
    assert cert['all_cycle_inequalities'] is True and s['all_cycle_inequalities'] is True
    # Potentials prove the universal lower bound. A concrete saved cycle attains it.
    cycle_costs = [sum((costs[v] for v in c), Q()) for c in model['cycles']]
    assert all(c >= 1 for c in cycle_costs) and min(cycle_costs) == 1
    witness_index = cycle_costs.index(Q(1)); witness = model['cycles'][witness_index]
    assert len(witness) == len(set(witness)) and set(witness) <= set(vertices)
    assert all(len(neighbours[v] & set(witness)) == 2 for v in witness)
    basis = read(folder/'basis.json')
    assert basis['model_sha256'] == sha(model_file)
    assert len(basis['variable_status']) == 574 and len(basis['row_status']) == len(model['rows'])
    assert basis['basic_variable_count'] == s['basic_variable_count']
    assert max(v.denominator.bit_length() for v in values) == s['maximum_denominator_bits']
    upper = fraction(prior['exact_upper'])
    assert objective <= upper
    target_file = folder/'target94-certificate.json'
    target = read(target_file)
    assert target['model_sha256'] == sha(model_file) and target['primal_sha256'] == sha(folder/'primal-certificate.json')
    assert target['source_sha256'] == sha(H/'scripts/target_point.py')
    other = min(neighbours[root])
    assert target['short_path'] == [root,other] and root.bit_count()%2 == 0 and other.bit_count()%2 == 1
    short = [fraction(v) for v in target['short_values']]
    expected_short = [Q(int(name in {f'x{root}',f'x{other}',f'e{other}',f'y{min(root,other)}_{max(root,other)}'})) for name in model['variables']]
    assert short == expected_short
    mixing = fraction(target['mixing_weight'])
    assert 0 < mixing < 1 and mixing == Q(92)/(objective-2)
    target_values = [fraction(v) for v in target['values']]
    assert len(target_values) == 574
    assert target_values == [mixing*a+(1-mixing)*b for a,b in zip(values,short)]
    for vector, wanted in ((short,Q(2)),(target_values,Q(94))):
        assert all(0 <= q <= 1 for q in vector)
        for row in model['rows']:
            lhs = sum((a*vector[i] for i,a in row['terms']), Q())
            assert (lhs == row['rhs'] if row['sense'] == 'eq' else lhs <= row['rhs'])
        assert sum((a*q for a,q in zip(model['objective'],vector)),Q()) == wanted
    assert fraction(target['objective']) == 94
    reports.append(dict(root=root, model_rows=len(model['rows']), variable_bounds_checked=574,
        exact_objective=rat(objective), excess_above_94=rat(objective-94), exact_upper=rat(upper), upper_minus_primal=rat(upper-objective),
        nonintegral_coordinates=sum(v.denominator != 1 for v in values), tight_model_rows=tight,
        edge_potential_count=337, potential_edge_inequalities=inequality_count, all_deleted_edge_targets_reachable=True,
        all_simple_cycle_inequalities_certified=True, minimum_cycle_cost=[1,1],
        attained_cycle_index=witness_index, attained_cycle_vertices=witness,
        target94=dict(short_path=[root,other], mixing_weight=rat(mixing), objective=[94,1],
            nonintegral_coordinates=sum(q.denominator != 1 for q in target_values),
            all_rows_and_bounds_checked=True, all_simple_cycles='Inherited by convexity from the checked point and the actual one-edge path.'),
        basis_reconstruction_repeated=False,
        pins={'model.json':sha(model_file),'primal-certificate.json':sha(folder/'primal-certificate.json'),'basis.json':sha(folder/'basis.json'),
              'target94-certificate.json':sha(target_file)}))
report = dict(status='PASS_EXACT_PRIMAL_AND_ALL_SIMPLE_CYCLE_CERTIFICATES',
    scope='All rational coordinates, saved rows, bounds and edge-deleted potential inequalities checked exactly. No optimizer, basis elimination, proof compiler, or software tests run. No Boolean-path or exact-optimality conclusion.',
    conclusion='For each fixed root, the continuous edge formulation augmented by every simple-cycle occupancy inequality admits both a feasible objective greater than 94 and an exact feasible point with objective 94. These constraints alone cannot exclude target cardinality 94.',
    models=reports,
    execution=dict(seconds=execution['seconds'], exit_code=execution['exit_code'], stop_reason=execution['stop_reason'],
        peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in execution['resource_samples']),
        minimum_sampled_free_bytes=min(s['free_bytes'] for s in execution['resource_samples'])),
    pins={str(p.relative_to(H)):sha(p) for p in [Path(__file__),H/'scripts/rational_basis.py',H/'scripts/run_rational.py',H/'scripts/target_point.py',H/'data/linear-audit.json',H/'data/rational-execution.json',H/'data/rational-summary.json']})
assert sha(H/'data/linear-audit.json') == baseline_hash and not (H/'data/lp-search.lock').exists()
(H/'data/rational-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
