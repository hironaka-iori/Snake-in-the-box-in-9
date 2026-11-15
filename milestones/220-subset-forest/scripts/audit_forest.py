"""Exact audit of saved subset rows, rational points, potentials and feasible flows."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm, isfinite
import hashlib
import json

H = Path(__file__).resolve().parents[1]
P = H.parent/'219-linear-partner'
def read(p): return json.loads(Path(p).read_bytes())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q): return [q.numerator,q.denominator]
def fraction(p):
    assert len(p)==2 and all(type(v) is int for v in p) and p[1]>0
    q=Q(*p); assert rat(q)==p
    return q
def check_vector(model, vector):
    assert len(vector)==len(model['variables']) and all(0<=q<=1 for q in vector)
    tight=0
    for row in model['rows']:
        lhs=sum((a*vector[i] for i,a in row['terms']),Q())
        assert row['sense'] in ('eq','le')
        assert (lhs==row['rhs'] if row['sense']=='eq' else lhs<=row['rhs']),row['name']
        tight+=lhs==row['rhs']
    return tight
def upper_certificate(model, cert):
    scale=cert['scale']; weights=cert['weights']
    assert type(scale) is int and scale==10**6 and len(weights)==len(model['rows'])
    rhs=0; residual=[scale*a for a in model['objective']]
    for row,w in zip(model['rows'],weights):
        assert type(w) is int and (row['sense']=='eq' or w>=0)
        rhs+=w*row['rhs']
        for i,a in row['terms']: residual[i]-=w*a
    positive=[max(r,0) for r in residual]
    assert residual==cert['residual'] and positive==cert['positive_residual']
    numerator=rhs+sum(positive)
    assert numerator==cert['upper_numerator'] and Q(numerator,scale)==fraction(cert['upper_bound'])
    return Q(numerator,scale)
def execution(kind):
    e=read(H/f'data/{kind}-execution.json')
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    for p,h in e['pins'].items(): assert sha(H/p)==h
    for stream in ('stdout','stderr'): assert sha(H/f'logs/{kind}-{stream}.log')==e[f'{stream}_sha256']
    assert sha(H/f'data/{kind}-summary.json')==e['summary_sha256']
    assert e['thread_environment']=={k:'1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
    g=e['resource_gate']; assert not g['errors'] and not g['processes'] and g['free_bytes']>=1024**3
    for s in e['resource_samples']:
        assert not s['errors'] and not s['lean_processes'] and s['free_bytes']>=768*1024**2
        assert s['private_bytes'] is None or s['private_bytes']<=256*1024**2
    return dict(seconds=e['seconds'],exit_code=0,stop_reason=None,
        peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in e['resource_samples']),
        minimum_sampled_free_bytes=min(s['free_bytes'] for s in e['resource_samples']),
        execution_sha256=sha(H/f'data/{kind}-execution.json'),summary_sha256=e['summary_sha256'])

preserved_paper_hash='c7492e5b4ee38feedd4fb4843aa9a93f31f16b6fe328da02820720b5e4b61378'
assert sha(H/'logs/review-upper-paper.md')==preserved_paper_hash
assert not (H/'data/forest-search.lock').exists()
assert sha(P/'data/linear-audit.json')=='b408c13775470f5bf903db4bdd52aa5d3444b0d7268847ff728018eaf5e11d37'
assert sha(P/'data/rational-audit.json')=='74ef6961a4e375f8edefb018ac2928a0ed8443f15a91f5b541ca01422b3c4855'
baseline=read(P/'data/linear-audit.json'); previous=read(P/'data/rational-audit.json')
for p,h in baseline['pins'].items(): assert sha(P/p)==h
for p,h in previous['pins'].items(): assert sha(P/p)==h
executions={kind:execution(kind) for kind in ('forest','rational','flow')}
summaries={kind:read(H/f'data/{kind}-summary.json') for kind in ('forest','rational','flow')}
for ss in summaries.values(): assert [s['root'] for s in ss]==[0,78]
reports=[]
for root in (0,78):
    F=H/'data'/f'forest-{root}'; R=H/'data'/f'rational-{root}'
    basefile=P/'data'/f'edge-{root}'/'model.json'; base=read(basefile)
    m=read(F/'model.json'); native=read(F/'native-result.json'); upper=read(F/'upper-certificate.json')
    prior=next(s for s in baseline['models'] if s['root']==root and s['form']=='edge')
    oldprimal=next(s for s in previous['models'] if s['root']==root)
    assert sha(basefile)==prior['source_pins']['model.json']==m['base_model_sha256']
    for key in ('root','form','variables','lower','upper','objective','vertices','edges','cycles','source_sha256','seed_sha256','graph_sha256'):
        assert m[key]==base[key],key
    assert m['source_sha256_220']==sha(H/'scripts/subset_separation.py')
    assert m['rows'][:len(base['rows'])]==base['rows']
    V=m['vertices']; edges=m['edges']; names={n:i for i,n in enumerate(m['variables'])}
    assert len(V)==158 and len(edges)==337 and len(names)==574
    xi={v:names[f'x{v}'] for v in V}; ei={v:names[f'e{v}'] for v in V if f'e{v}' in names}
    yi={(u,v):names[f'y{u}_{v}'] for u,v in edges}
    witnesses=m['subset_witnesses']; assert len(witnesses)==25 and len(m['rows'])==len(base['rows'])+25
    keys=set()
    for k,w in enumerate(witnesses):
        U=w['subset']; v=w['vertex']; S=set(U)
        assert U==sorted(S) and S<=set(V) and v in S
        key=(v,tuple(U)); assert key not in keys; keys.add(key)
        assert w['row_index']==len(base['rows'])+k and type(w['iteration']) is int and w['iteration']>=0
        assert isfinite(w['violation_at_discovery']) and w['violation_at_discovery']>1e-7
        terms={xi[u]:-1 for u in U}; terms[xi[v]]+=1
        for u,t in edges:
            if u in S and t in S: terms[yi[u,t]]=1
        expected=dict(name=f'forest_{k}',terms=[[i,a] for i,a in sorted(terms.items()) if a],sense='le',rhs=0)
        assert m['rows'][w['row_index']]==expected
    assert native['model_sha256']==upper['model_sha256']==sha(F/'model.json')
    assert native['status']=='OPTIMAL_NATIVE' and native['added_subset_count']==25
    assert len(native['values'])==574 and len(native['duals'])==len(m['rows'])
    assert all(isfinite(v) for v in native['values']+native['duals'])
    exactupper=upper_certificate(m,upper)
    assert exactupper==fraction(native['exact_upper'])
    assert upper['weights']==[max(0,round(w*10**6)) if row['sense']=='le' else round(w*10**6) for row,w in zip(m['rows'],native['duals'])]
    fsummary=next(s for s in summaries['forest'] if s['root']==root)
    assert fsummary=={k:v for k,v in native.items() if k not in ('values','duals','steps')}
    steps=native['steps']; assert [s['iteration'] for s in steps]==list(range(len(steps)))
    for step in steps:
        assert step['rows']==len(base['rows'])+sum(w['iteration']<step['iteration'] for w in witnesses)
        if step['iteration']<60: assert step['new_violated_subsets']==sum(w['iteration']==step['iteration'] for w in witnesses)
    assert native['no_new_violations_at_tolerance'] is True and steps[-1]['new_violated_subsets']==0
    initial=read(F/'initial-separation.json'); assert [r['point'] for r in initial]==['primal','target94']
    initial_reports=[]
    for record in initial:
        oldfile=P/'data'/f'rational-{root}'/(record['point']+'-certificate.json')
        assert sha(oldfile)==record['source_sha256']==oldprimal['pins'][oldfile.name]
        old=[fraction(q) for q in read(oldfile)['values']]
        assert record['scale']==lcm(*(q.denominator for q in old))
        check_vector(base,old)
        violations=[]; seen=set()
        for w in record['violated_witnesses']:
            U=w['subset']; v=w['vertex']; S=set(U)
            assert U==sorted(S) and S<=set(V) and v in S and v not in seen; seen.add(v)
            X=sum((old[xi[u]] for u in U),Q())
            Y=sum((old[yi[u,t]] for u,t in edges if u in S and t in S),Q())
            boundary=sum((old[yi[u,t]] for u,t in edges if (u in S)!=(t in S)),Q())
            endpoint=sum((Q(1) if u==root else old[ei[u]] if u in ei else Q() for u in U),Q())
            violation=Y-X+old[xi[v]]
            assert violation>0 and violation==fraction(w['violation'])
            assert boundary+endpoint==fraction(w['cut_value'])
            assert 2*violation==2*old[xi[v]]-boundary-endpoint
            violations.append(violation)
        assert record['positive_count']==len(violations)
        assert fraction(record['largest_violation'])==max(violations,default=Q())
        initial_reports.append(dict(point=record['point'],witness_count=len(violations),largest_violation=rat(max(violations,default=Q()))))
    c=read(R/'primal-certificate.json'); values=[fraction(q) for q in c['values']]
    assert c['model_sha256']==sha(F/'model.json') and c['source_sha256']==sha(H/'scripts/rational_basis.py')
    tight=check_vector(m,values)
    objective=sum((a*q for a,q in zip(m['objective'],values)),Q())
    assert objective==fraction(c['objective']) and 94<objective<=exactupper
    rs=next(s for s in summaries['rational'] if s['root']==root)
    assert fraction(rs['objective'])==objective and rs['objective_float']==float(objective)
    assert rs['certificate_sha256']==sha(R/'primal-certificate.json')
    assert rs['maximum_denominator_bits']==max(q.denominator.bit_length() for q in values)
    index={v:i for i,v in enumerate(V)}; N={v:set() for v in V}; costs={v:1-values[xi[v]] for v in V}
    for u,v in edges: N[u].add(v); N[v].add(u)
    assert [p['edge'] for p in c['potentials']]==edges
    cyclebounds=[]; potential_checks=0
    for cp in c['potentials']:
        s,t=cp['edge']; pot=[fraction(q) for q in cp['distance']]
        assert len(pot)==158 and pot[index[s]]==0
        reached={s}; todo=[s]
        while todo:
            u=todo.pop()
            for v in N[u]:
                if (min(u,v),max(u,v))==(s,t) or v in reached: continue
                reached.add(v); todo.append(v)
        assert t in reached and cp['target_reachable'] is True
        for u,v in edges:
            if (u,v)==(s,t):continue
            assert abs(pot[index[u]]-pot[index[v]])<=costs[u]+costs[v]
            potential_checks+=1
        bound=(pot[index[t]]+costs[s]+costs[t])/2
        assert bound>=1 and bound==fraction(cp['cycle_lower_bound']); cyclebounds.append(bound)
    assert potential_checks==337*336 and min(cyclebounds)==fraction(c['minimum_cycle_cost'])==fraction(rs['minimum_cycle_cost'])==1
    assert c['all_cycle_inequalities'] is True and rs['all_cycle_inequalities'] is True
    static_costs=[sum((costs[v] for v in cyc),Q()) for cyc in m['cycles']]
    assert min(static_costs)==1
    flow=read(R/'forest-flow-certificate.json')
    assert flow['model_sha256']==sha(F/'model.json') and flow['primal_sha256']==sha(R/'primal-certificate.json')
    assert flow['source_sha256']==sha(H/'scripts/flow_certificate.py')
    D=flow['scale']; assert D==lcm(*(q.denominator for q in values))
    assert all((q*D).denominator==1 for q in values)
    z=[int(q*D) for q in values]
    E={v:D if v==root else z[ei[v]] if v in ei else 0 for v in V}
    assert z[xi[root]]==D and sum(E.values())==2*D
    for v in V:
        degree=sum(z[yi[min(v,w),max(v,w)]] for w in N[v])
        assert degree==2*z[xi[v]]-E[v]
    expected_arcs=[]
    for u,v in edges:
        cap=z[yi[u,v]]; expected_arcs.extend([[index[u],index[v],cap],[index[v],index[u],cap]])
    expected_arcs.extend([[index[v],158,E[v]] for v in V])
    assert flow['vertices']==V and flow['sink']==158 and flow['arcs']==expected_arcs and len(expected_arcs)==832
    assert all(type(a) is int for row in expected_arcs for a in row) and all(a[2]>=0 for a in expected_arcs)
    assert sum(a[2] for a in expected_arcs)<2**62
    assert [f['source'] for f in flow['flows']]==V and flow['violations']==[] and flow['all_subset_inequalities'] is True
    nonzero_count=0; supply_margins=[]
    for f in flow['flows']:
        source=f['source']; sparse=f['nonzero_arcs']
        assert all(len(a)==2 and all(type(t) is int for t in a) for a in sparse)
        assert [a[0] for a in sparse]==sorted({a[0] for a in sparse})
        amounts=[0]*832
        for arc_id,amount in sparse:
            assert 0<=arc_id<832 and amount>0; amounts[arc_id]=amount
        balance=[0]*159
        for (u,v,cap),amount in zip(expected_arcs,amounts):
            assert 0<=amount<=cap
            balance[u]+=amount; balance[v]-=amount
        value=f['value']; assert type(value) is int and value>=2*z[xi[source]]
        assert balance[index[source]]==value and balance[158]==-value
        assert all(b==0 for i,b in enumerate(balance) if i not in (index[source],158))
        nonzero_count+=len(sparse); supply_margins.append(value-2*z[xi[source]])
    fs=next(s for s in summaries['flow'] if s['root']==root)
    assert fs['certificate_sha256']==sha(R/'forest-flow-certificate.json') and fs['scale']==D
    assert fs['flow_count']==158 and fs['violations']==0 and fs['all_subset_inequalities'] is True
    target=read(R/'target94-certificate.json')
    assert target['model_sha256']==sha(F/'model.json') and target['primal_sha256']==sha(R/'primal-certificate.json')
    assert target['source_sha256']==sha(H/'scripts/target_point.py')
    other=min(N[root]); assert target['short_path']==[root,other] and other.bit_count()%2==1
    selected_names={f'x{root}',f'x{other}',f'e{other}',f'y{min(root,other)}_{max(root,other)}'}
    short=[fraction(q) for q in target['short_values']]
    assert short==[Q(int(n in selected_names)) for n in m['variables']]
    mixing=fraction(target['mixing_weight']); assert 0<mixing<1 and mixing==Q(92)/(objective-2)
    tv=[fraction(q) for q in target['values']]
    assert len(tv)==574 and tv==[mixing*a+(1-mixing)*b for a,b in zip(values,short)]
    check_vector(m,short); check_vector(m,tv)
    assert sum((a*q for a,q in zip(m['objective'],short)),Q())==2
    assert sum((a*q for a,q in zip(m['objective'],tv)),Q())==fraction(target['objective'])==94
    reports.append(dict(root=root,base_rows=len(base['rows']),added_subset_rows=25,total_rows=len(m['rows']),variables=574,
        exact_upper=rat(exactupper),exact_primal=rat(objective),upper_minus_primal=rat(exactupper-objective),
        objective_excess_above94=rat(objective-94),initial219_violations=initial_reports,
        tight_rows=tight,nonintegral_primal_coordinates=sum(q.denominator!=1 for q in values),
        all_cycle_potentials=337,exact_cycle_potential_inequalities=potential_checks,
        minimum_cycle_cost=[1,1],attaining_static_cycle=m['cycles'][static_costs.index(Q(1))],
        all_subset_flows=158,directed_arcs=832,exact_arc_capacity_checks=158*832,
        flow_scale=D,nonzero_flow_entries=nonzero_count,minimum_supply_surplus=min(supply_margins),
        exact_degree_equations=158,all_subset_inequalities_certified=True,
        target94=dict(objective=[94,1],short_path=[root,other],mixing_weight=rat(mixing),
            nonintegral_coordinates=sum(q.denominator!=1 for q in tv),all_rows_and_bounds_checked=True,
            all_cycle_and_subset_inequalities='Inherited by convexity from the checked rational point and actual one-edge path.'),
        pins={str(p.relative_to(H)):sha(p) for p in list(F.iterdir())+list(R.iterdir()) if p.is_file()}))
report=dict(status='PASS_EXACT_SUBSET_ROWS_UPPERS_PRIMALS_CYCLES_FLOWS_AND_TARGET94',
    scope='Saved integer/rational arithmetic only. No optimizer, compiler, search, software tests, or repeated basis elimination. Complete flow feasibility is verified; no maximum-flow optimality is needed.',
    conclusion='Both fixed-root continuous edge models augmented by every simple-cycle occupancy inequality and every subset inequality Y(U)<=X(U)-x_v admit an exact feasible point of cardinality94. The result does not establish any Boolean partner or global snake bound.',
    models=reports,executions=executions,
    generic_lean_bridge='The source Forest220.lean separately states actual-path edge counting and integer degree-boundary equivalence. This finite data audit neither compiles that source nor certifies a Lean composition of all saved arrays and rational flow arguments.',
    pins={str(p.relative_to(H)):sha(p) for p in [Path(__file__),H/'scripts/subset_separation.py',H/'scripts/rational_basis.py',H/'scripts/flow_certificate.py',H/'scripts/target_point.py',H/'logs/review-upper-paper.md']})
assert sha(H/'logs/review-upper-paper.md')==preserved_paper_hash
(H/'data/forest-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
