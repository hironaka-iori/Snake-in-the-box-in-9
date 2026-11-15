"""Exact inspection of saved long-model points, flows, and cycle potentials.

This reads research certificates only; it runs no optimizer or proof compiler.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import hashlib
import json

H = Path(__file__).resolve().parents[1]

def read(p):
    return json.loads(Path(p).read_bytes())

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def rat(q):
    return [q.numerator, q.denominator]

def fraction(pair):
    assert len(pair) == 2 and all(type(v) is int for v in pair) and pair[1] > 0
    q = Q(*pair)
    assert rat(q) == pair
    return q

def vector_check(model, values):
    assert len(values) == len(model['variables']) == 574
    assert model['lower'] == [0] * 574 and model['upper'] == [1] * 574
    assert all(0 <= v <= 1 for v in values)
    tight = 0
    for row in model['rows']:
        assert row['sense'] in ('eq', 'le')
        assert type(row['rhs']) is int
        assert all(type(i) is int and 0 <= i < 574 and type(a) is int
                   for i, a in row['terms'])
        lhs = sum((a * values[i] for i, a in row['terms']), Q())
        assert (lhs == row['rhs'] if row['sense'] == 'eq' else lhs <= row['rhs']), row['name']
        tight += lhs == row['rhs']
    return tight

def execution(kind):
    path = H / f'data/{kind}-execution.json'
    e = read(path)
    assert e['status'] == 'ACCEPTED_NATIVE_RESULT' and e['exit_code'] == 0
    assert e['stop_reason'] is None
    for p, h in e['pins'].items():
        assert sha(H / p) == h
    for stream in ('stdout', 'stderr'):
        assert sha(H / f'logs/{kind}-{stream}.log') == e[f'{stream}_sha256']
    assert sha(H / f'data/{kind}-summary.json') == e['summary_sha256']
    assert e['thread_environment'] == {k: '1' for k in
        ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS')}
    gate = e['resource_gate']
    assert not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3
    for s in e['resource_samples']:
        assert not s['errors'] and not s['lean_processes'] and s['free_bytes'] >= 768*1024**2
        assert s['private_bytes'] is None or s['private_bytes'] <= 256*1024**2
    return dict(exit_code=0, stop_reason=None, seconds=e['seconds'],
        peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in e['resource_samples']),
        minimum_sampled_free_bytes=min(s['free_bytes'] for s in e['resource_samples']),
        receipt_sha256=sha(path), summary_sha256=e['summary_sha256'])

frozen = {
    'scripts/audit_square.py': '7ab3b56a9220487b99ed08c3df28ba0d21513191434b6a32b40cecf6c56eb244',
    'data/square-audit.json': 'cc4c44f77167f7daa681d03de7ab28c2714f2c60307945511ff078353e534993',
    'logs/square-review.md': '763f9cd1e446abf3ed5065d671fabe2f5289c398012086730fb067e5dc3d1d78',
    'scripts/audit_rational.py': '5985e76cfc4c33cb095f32a485c633a21f7fed8c6f8370b32b0513d98d8509f3',
    'data/rational-audit.json': 'e852d65841e1027075eec54ada3a71071a72515858afcf029ac1ebc4e8ea21d0',
    'logs/rational-review.md': 'eaed10a0cb93ace73c44daa5b05a49679bea22628de904f183f88b20b5c17ca0',
}
for p, h in frozen.items():
    assert sha(H / p) == h

baseline = read(H / 'data/long-audit.json')
assert baseline['status'] == 'PASS_EXACT_LONG_CYCLE_ROWS_AND_UPPER_CERTIFICATES'
for p, h in baseline['pins'].items():
    assert sha(H / p) == h
for row in baseline['models']:
    for p, h in row['pins'].items():
        assert sha(H / p) == h
executions = {kind: execution(kind) for kind in ('rational-long', 'flow-long')}
summaries = {kind: read(H / f'data/{kind}-summary.json')
             for kind in ('rational-long', 'flow-long', 'cut-long')}
for rows in summaries.values():
    assert [s['root'] for s in rows] == [0, 78]

reports = []
all_pins = {}
for root in (0, 78):
    M = H / 'data' / f'long-{root}'
    R = H / 'data' / f'rational-long-{root}'
    model_file = M / 'model.json'
    primal_file = R / 'primal-certificate.json'
    m = read(model_file)
    cert = read(primal_file)
    b = next(s for s in baseline['models'] if s['root'] == root)
    rs = next(s for s in summaries['rational-long'] if s['root'] == root)
    assert m['root'] == root and len(m['rows']) == b['total_rows']
    assert cert['model_sha256'] == sha(model_file) == b['pins'][f'data\\long-{root}\\model.json']
    assert cert['source_sha256'] == sha(H / 'scripts/rational_long.py')
    assert sha(primal_file) == rs['certificate_sha256']
    base = read(H / 'data' / f'square-{root}' / 'model.json')
    for key in ('variables', 'lower', 'upper', 'objective', 'vertices', 'edges', 'cycles'):
        assert m[key] == base[key], key
    assert m['rows'][:len(base['rows'])] == base['rows']

    values = [fraction(p) for p in cert['values']]
    tight = vector_check(m, values)
    objective = sum((a*v for a, v in zip(m['objective'], values)), Q())
    upper = fraction(b['dual_certificate']['exact_upper'])
    assert objective == fraction(cert['objective']) == fraction(rs['objective'])
    assert 94 < objective <= upper < 96
    assert rs['objective_float'] == float(objective)
    assert max(v.denominator.bit_length() for v in values) == rs['maximum_denominator_bits']
    V, edges = m['vertices'], m['edges']
    assert len(V) == len(set(V)) == 158 and len(edges) == len({tuple(e) for e in edges}) == 337
    names = {n: i for i, n in enumerate(m['variables'])}
    assert len(names) == 574 and m['variables'][:158] == [f'x{v}' for v in V]
    assert m['objective'] == [1]*158 + [0]*416
    pos = {v: i for i, v in enumerate(V)}
    xi = {v: names[f'x{v}'] for v in V}
    ei = {v: names[f'e{v}'] for v in V if f'e{v}' in names}
    yi = {(u, v): names[f'y{u}_{v}'] for u, v in edges}
    N = {v: set() for v in V}
    for u, v in edges:
        assert u < v and (u ^ v).bit_count() == 1
        N[u].add(v)
        N[v].add(u)
    assert set(ei) == {v for v in V if v.bit_count() % 2 == 1}

    # All simple-cycle occupancy inequalities, checked without shortest-path search.
    costs = {v: 1-values[xi[v]] for v in V}
    assert [p['edge'] for p in cert['potentials']] == edges
    occupancy_checks, occupancy_bounds = 0, []
    for p in cert['potentials']:
        s, t = p['edge']
        potentials = [fraction(q) for q in p['distance']]
        assert len(potentials) == 158 and potentials[pos[s]] == 0
        reached, todo = {s}, [s]
        while todo:
            u = todo.pop()
            for v in N[u]:
                if (min(u, v), max(u, v)) == (s, t) or v in reached:
                    continue
                reached.add(v)
                todo.append(v)
        assert t in reached and p['target_reachable'] is True
        for u, v in edges:
            if (u, v) == (s, t):
                continue
            assert abs(potentials[pos[u]]-potentials[pos[v]]) <= costs[u]+costs[v]
            occupancy_checks += 1
        bound = (potentials[pos[t]]+costs[s]+costs[t])/2
        assert bound >= 1 and bound == fraction(p['cycle_lower_bound'])
        occupancy_bounds.append(bound)
    assert occupancy_checks == 337*336
    assert min(occupancy_bounds) == fraction(cert['minimum_cycle_cost']) == fraction(rs['minimum_cycle_cost']) == 1
    assert cert['all_cycle_inequalities'] is True and rs['all_cycle_inequalities'] is True
    static_costs = [sum((costs[v] for v in cyc), Q()) for cyc in m['cycles']]
    assert min(static_costs) == 1

    # All subset-forest inequalities from feasible flows and exact degree equations.
    flow_file = R / 'forest-flow-certificate.json'
    flow = read(flow_file)
    fs = next(s for s in summaries['flow-long'] if s['root'] == root)
    assert flow['model_sha256'] == sha(model_file) and flow['primal_sha256'] == sha(primal_file)
    assert flow['source_sha256'] == sha(H / 'scripts/flow_long.py')
    assert sha(flow_file) == fs['certificate_sha256']
    D = lcm(*(v.denominator for v in values))
    assert type(flow['scale']) is int and flow['scale'] == fs['scale'] == D
    assert fs['scale_bits'] == D.bit_length()
    assert all((q*D).denominator == 1 for q in values)
    z = [int(q*D) for q in values]
    E = {v: D if v == root else z[ei[v]] if v in ei else 0 for v in V}
    assert z[xi[root]] == D and sum(E.values()) == 2*D
    for v in V:
        degree = sum(z[yi[min(v,w), max(v,w)]] for w in N[v])
        assert degree == 2*z[xi[v]]-E[v]
    arcs = []
    for u, v in edges:
        cap = z[yi[u,v]]
        arcs.extend([[pos[u], pos[v], cap], [pos[v], pos[u], cap]])
    arcs.extend([[pos[v], 158, E[v]] for v in V])
    assert flow['vertices'] == V and flow['sink'] == 158 and flow['arcs'] == arcs and len(arcs) == 832
    assert all(type(a) is int for row in arcs for a in row) and all(row[2] >= 0 for row in arcs)
    assert [f['source'] for f in flow['flows']] == V
    assert flow['violations'] == [] and flow['all_subset_inequalities'] is True
    assert fs['flow_count'] == 158 and fs['violations'] == 0 and fs['all_subset_inequalities'] is True
    nonzero_flow_entries, margins = 0, []
    for f in flow['flows']:
        source = f['source']
        sparse = f['nonzero_arcs']
        assert all(len(a) == 2 and all(type(t) is int for t in a) for a in sparse)
        assert [a[0] for a in sparse] == sorted({a[0] for a in sparse})
        amounts = [0]*832
        for arc_id, amount in sparse:
            assert 0 <= arc_id < 832 and amount > 0
            amounts[arc_id] = amount
        balance = [0]*159
        for (u, v, cap), amount in zip(arcs, amounts):
            assert 0 <= amount <= cap
            balance[u] += amount
            balance[v] -= amount
        value = f['value']
        assert type(value) is int and value >= 2*z[xi[source]]
        assert balance[pos[source]] == value and balance[158] == -value
        assert all(v == 0 for i, v in enumerate(balance) if i not in (pos[source], 158))
        margins.append(value-2*z[xi[source]])
        nonzero_flow_entries += len(sparse)

    # All odd-marked disagreement-cycle inequalities from two-copy potentials.
    cut_file = H / 'data' / f'cut-long-{root}.json'
    cut = read(cut_file)
    cs = next(s for s in summaries['cut-long'] if s['root'] == root)
    assert cut['root'] == root and cut['model_sha256'] == sha(model_file)
    assert cut['primal_sha256'] == sha(primal_file) and cut['source_sha256'] == sha(H / 'scripts/cut_long.py')
    assert type(cut['scale']) is int and cut['scale'] == D
    assert cut['violations'] == [] and cut['complete_cycle_parity'] is True
    assert [p['source'] for p in cut['potentials']] == V
    parity_arcs, disagreements = [], {}
    for u, v in edges:
        d = z[xi[u]]+z[xi[v]]-2*z[yi[u,v]]
        assert type(d) is int and 0 <= d <= D
        disagreements[u,v] = d
        for bit in (0,1):
            for flip in (0,1):
                a, bstate = 2*pos[u]+bit, 2*pos[v]+(bit ^ flip)
                cost = D-d if flip else d
                parity_arcs.extend([(a,bstate,cost), (bstate,a,cost)])
    assert len(parity_arcs) == 337*8 and len(set(parity_arcs)) == 337*8
    parity_checks, parity_bounds = 0, []
    for p in cut['potentials']:
        potential = p['values']
        assert len(potential) == 316 and all(type(v) is int for v in potential)
        source = 2*pos[p['source']]
        assert potential[source] == 0 and potential[source+1] >= D
        for u, v, cost in parity_arcs:
            assert potential[v]-potential[u] <= cost
            parity_checks += 1
        parity_bounds.append(potential[source+1])
    assert parity_checks == 158*337*8
    assert min(parity_bounds) == cut['minimum_scaled_odd_walk_cost'] == D
    assert cs == dict(root=root, violated_cycles=0, minimum_cost=[D,D], lengths=[], complete_cycle_parity=True)
    # An explicit square witness establishes attainment; no shortest-path optimality is assumed.
    parity_witness = None
    for cyc in m['cycles']:
        if len(cyc) != 4:
            continue
        S = set(cyc)
        assert len(S) == 4 and all(len(N[v] & S) == 2 for v in S)
        ordered = [min(S)]
        ordered.append(min(N[ordered[0]] & S))
        while len(ordered) < 4:
            nxt = (N[ordered[-1]] & S) - set(ordered)
            assert len(nxt) == 1
            ordered.append(next(iter(nxt)))
        assert ordered[0] in N[ordered[-1]]
        ds = [disagreements[min(ordered[i],ordered[(i+1)%4]), max(ordered[i],ordered[(i+1)%4])]
              for i in range(4)]
        for mask in range(16):
            if mask.bit_count() % 2 != 1:
                continue
            cost = sum(D-d if mask & (1<<i) else d for i,d in enumerate(ds))
            assert cost >= D
            if cost == D and parity_witness is None:
                parity_witness = dict(cycle=ordered, odd_edge_indices=[i for i in range(4) if mask & (1<<i)], scaled_cost=D)
    assert parity_witness is not None

    # Saved exact target-94 mixtures; each complete family is linear in these coordinates.
    target_file = R / 'target94-certificate.json'
    target = read(target_file)
    assert target['model_sha256'] == sha(model_file) and target['primal_sha256'] == sha(primal_file)
    assert target['source_sha256'] == sha(H / 'scripts/target_point_long.py')
    other = min(N[root])
    assert target['short_path'] == [root, other] and other.bit_count()%2 == 1
    assert (root ^ other).bit_count() == 1 and root.bit_count()%2 == 0
    selected = {f'x{root}',f'x{other}',f'e{other}',f'y{min(root,other)}_{max(root,other)}'}
    short = [fraction(q) for q in target['short_values']]
    assert short == [Q(int(name in selected)) for name in m['variables']]
    mixing = fraction(target['mixing_weight'])
    assert 0 < mixing < 1 and mixing == Q(92)/(objective-2)
    tv = [fraction(q) for q in target['values']]
    assert len(tv) == 574 and tv == [mixing*a+(1-mixing)*b for a,b in zip(values,short)]
    vector_check(m, short)
    vector_check(m, tv)
    assert sum((a*q for a,q in zip(m['objective'],short)),Q()) == 2
    assert sum((a*q for a,q in zip(m['objective'],tv)),Q()) == fraction(target['objective']) == 94

    paths = [model_file, primal_file, flow_file, cut_file, target_file]
    model_pins = {str(p.relative_to(H)): sha(p) for p in paths}
    all_pins.update(model_pins)
    reports.append(dict(root=root,rows=len(m['rows']),variables=574,tight_rows=tight,
        exact_primal=rat(objective),previously_audited_exact_upper=rat(upper),upper_minus_primal=rat(upper-objective),
        nonintegral_primal_coordinates=sum(v.denominator!=1 for v in values),
        maximum_denominator_bits=max(v.denominator.bit_length() for v in values),
        occupancy=dict(potentials=337,edge_inequalities=occupancy_checks,minimum_cost=[1,1],
            attaining_static_cycle=m['cycles'][static_costs.index(Q(1))]),
        forest=dict(flows=158,directed_arcs=832,capacity_checks=158*832,degree_equations=158,
            scale=D,scale_bits=D.bit_length(),total_arc_capacity=sum(a[2] for a in arcs),
            total_arc_capacity_bits=sum(a[2] for a in arcs).bit_length(),
            nonzero_flow_entries=nonzero_flow_entries,minimum_supply_surplus=min(margins),
            all_subset_inequalities_certified=True,integer_arithmetic='Unbounded Python integers throughout the independent audit.'),
        disagreement_parity=dict(potentials=158,states=316,directed_arcs=2696,
            directed_arc_inequalities=parity_checks,minimum_cost=[1,1],attaining_square=parity_witness,
            all_cycle_odd_subset_inequalities_certified=True),
        target94=dict(objective=[94,1],short_path=[root,other],mixing_weight=rat(mixing),
            nonintegral_coordinates=sum(v.denominator!=1 for v in tv),all_saved_rows_and_bounds=True,
            complete_families='Occupancy cycles, subset-forest inequalities, and odd-marked disagreement cycles are inherited by convexity from the audited point and actual one-edge path.'),
        pins=model_pins))

for p in [Path(__file__),H/'data/long-audit.json',H/'data/square-audit.json',H/'data/rational-audit.json',
          H/'scripts/rational_long.py',H/'scripts/flow_long.py',H/'scripts/cut_long.py',H/'scripts/target_point_long.py',
          H/'scripts/run_rational_long.py',H/'scripts/run_flow_long.py',
          H/'data/rational-long-execution.json',H/'data/flow-long-execution.json',
          H/'data/rational-long-summary.json',H/'data/flow-long-summary.json',H/'data/cut-long-summary.json']:
    all_pins[str(p.relative_to(H))] = sha(p)
report = dict(status='PASS_EXACT_LONG_PRIMALS_ALL_THREE_FAMILIES_AND_TARGET94',
    scope='Independent saved integer/rational arithmetic. All model rows, bounds, occupancy potentials, feasible flows, degree identities, two-copy parity potentials and target mixtures checked. No optimizer, compiler, search, basis reconstruction, or software tests.',
    conclusion='For each fixed root, the saved continuous model plus all occupancy-cycle, subset-forest, and odd-marked disagreement-cycle inequalities admits an exact cardinality-94 point. No Boolean partner or global snake conclusion follows.',
    baseline_dependency='Added-row validity and exact upper certificates are the separately frozen long-audit.json review; their sources and model bytes are matched here, without repeating that audit.',
    lean_scope='This is exact native-array arithmetic. Generic Lean results are separate; no end-to-end Lean assembly of these concrete vectors, flows and potentials is asserted.',
    models=reports,executions=executions,pins=all_pins)
for p,h in frozen.items():
    assert sha(H/p) == h
(H/'data/long-primal-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:report[k] for k in ('status','models','executions')},indent=2))
