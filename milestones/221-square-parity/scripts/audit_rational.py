"""Separate exact audit of the frozen square-model rational points."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
H=Path(__file__).resolve().parents[1]
def read(p):return json.loads(Path(p).read_bytes())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q):return [q.numerator,q.denominator]
def fraction(p):
    assert len(p)==2 and all(type(v) is int for v in p) and p[1]>0
    q=Q(*p);assert rat(q)==p
    return q
def vector_check(m,z):
    assert len(z)==574 and all(0<=v<=1 for v in z)
    tight=0
    for row in m['rows']:
        lhs=sum((a*z[i] for i,a in row['terms']),Q())
        assert (lhs==row['rhs'] if row['sense']=='eq' else lhs<=row['rhs']),row['name']
        tight+=lhs==row['rhs']
    return tight

frozen={'data/square-audit.json':'cc4c44f77167f7daa681d03de7ab28c2714f2c60307945511ff078353e534993',
        'logs/square-review.md':'763f9cd1e446abf3ed5065d671fabe2f5289c398012086730fb067e5dc3d1d78',
        'scripts/audit_square.py':'7ab3b56a9220487b99ed08c3df28ba0d21513191434b6a32b40cecf6c56eb244'}
for p,h in frozen.items():assert sha(H/p)==h
prior=read(H/'data/square-audit.json')
for p,h in prior['pins'].items():assert sha(p)==h
e=read(H/'data/rational-execution.json')
assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
for p,h in e['pins'].items():assert sha(H/p)==h
for stream in ('stdout','stderr'):assert sha(H/f'logs/rational-{stream}.log')==e[f'{stream}_sha256']
assert sha(H/'data/rational-summary.json')==e['summary_sha256']
assert e['thread_environment']=={k:'1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
gate=e['resource_gate'];assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
for s in e['resource_samples']:
    assert not s['errors'] and not s['lean_processes'] and s['free_bytes']>=768*1024**2
    assert s['private_bytes'] is None or s['private_bytes']<=256*1024**2
summary=read(H/'data/rational-summary.json');assert [s['root'] for s in summary]==[0,78]
reports=[]
for s in summary:
    root=s['root'];R=H/'data'/f'rational-{root}';model_file=H/'data'/f'square-{root}'/'model.json'
    m=read(model_file);c=read(R/'primal-certificate.json');z=[fraction(q) for q in c['values']]
    b=next(r for r in prior['models'] if r['root']==root)
    assert sha(model_file)==c['model_sha256']==b['pins'][f'data\\square-{root}\\model.json']
    assert c['source_sha256']==sha(H/'scripts/rational_basis.py') and s['certificate_sha256']==sha(R/'primal-certificate.json')
    assert m['lower']==[0]*574 and m['upper']==[1]*574
    tight=vector_check(m,z)
    objective=sum((a*v for a,v in zip(m['objective'],z)),Q())
    assert objective==fraction(c['objective'])==fraction(s['objective']) and objective>94
    assert s['objective_float']==float(objective)
    upper=fraction(b['exact_upper']);assert objective<=upper
    V=m['vertices'];edges=m['edges'];index={v:i for i,v in enumerate(V)}
    assert len(V)==158 and len(edges)==337 and m['variables'][:158]==[f'x{v}' for v in V]
    assert m['objective']==[1]*158+[0]*416
    N={v:set() for v in V};costs={v:1-z[index[v]] for v in V}
    for u,v in edges:N[u].add(v);N[v].add(u)
    assert [p['edge'] for p in c['potentials']]==edges
    count=0;bounds=[]
    for p in c['potentials']:
        source,target=p['edge'];pot=[fraction(q) for q in p['distance']]
        assert len(pot)==158 and pot[index[source]]==0
        reached={source};todo=[source]
        while todo:
            u=todo.pop()
            for v in N[u]:
                if (min(u,v),max(u,v))==(source,target) or v in reached:continue
                reached.add(v);todo.append(v)
        assert target in reached and p['target_reachable'] is True
        for u,v in edges:
            if (u,v)==(source,target):continue
            assert abs(pot[index[u]]-pot[index[v]])<=costs[u]+costs[v];count+=1
        bound=(pot[index[target]]+costs[source]+costs[target])/2
        assert bound>=1 and bound==fraction(p['cycle_lower_bound']);bounds.append(bound)
    assert count==113232 and min(bounds)==fraction(c['minimum_cycle_cost'])==fraction(s['minimum_cycle_cost'])==1
    assert c['all_cycle_inequalities'] is True and s['all_cycle_inequalities'] is True
    cycle_costs=[sum((costs[v] for v in cycle),Q()) for cycle in m['cycles']]
    assert min(cycle_costs)==1
    assert max(q.denominator.bit_length() for q in z)==s['maximum_denominator_bits']==59
    # Independently form a target-94 mixture; no extra producer certificate is assumed.
    other=min(N[root]);selected={f'x{root}',f'x{other}',f'e{other}',f'y{min(root,other)}_{max(root,other)}'}
    short=[Q(int(n in selected)) for n in m['variables']]
    vector_check(m,short)
    assert (root^other).bit_count()==1 and root.bit_count()%2==0 and other.bit_count()%2==1
    assert sum((a*v for a,v in zip(m['objective'],short)),Q())==2
    mixing=Q(92)/(objective-2);assert 0<mixing<1
    target=[mixing*a+(1-mixing)*d for a,d in zip(z,short)]
    vector_check(m,target)
    assert sum((a*v for a,v in zip(m['objective'],target)),Q())==94
    reports.append(dict(root=root,rows=len(m['rows']),coordinates=574,tight_rows=tight,
        exact_objective=rat(objective),exact_upper=rat(upper),gap=rat(upper-objective),
        nonintegral_coordinates=sum(q.denominator!=1 for q in z),maximum_denominator_bits=59,
        all_occupancy_cycle_inequalities=True,potentials=337,potential_edge_inequalities=count,
        minimum_cycle_cost=[1,1],attaining_static_cycle=m['cycles'][cycle_costs.index(Q(1))],
        reviewer_target94=dict(short_path=[root,other],mixing_weight=rat(mixing),objective=[94,1],
            nonintegral_coordinates=sum(q.denominator!=1 for q in target),all_saved_rows_and_bounds=True,
            all_occupancy_cycles='Inherited by convexity from the certified point and actual one-edge path.'),
        full_subset_family='Not certified by this audit; only the saved subset rows are checked.',
        longer_disagreement_parity_cycles='Not covered by occupancy-cycle potentials.',
        pins={'model.json':sha(model_file),'primal-certificate.json':sha(R/'primal-certificate.json')}))
report=dict(status='PASS_EXACT_SQUARE_MODEL_PRIMALS_AND_OCCUPANCY_CYCLE_POTENTIALS',
    scope='Exact saved-row, variable-bound, and occupancy-potential arithmetic only. No optimizer, compiler, search, flow computation, basis elimination, or software tests.',
    conclusion='The saved square models and all simple-cycle occupancy inequalities admit exact rational points and reviewer-derived mixtures of cardinality94. The entire subset family and longer disagreement-parity inequalities remain outside this audit.',
    models=reports,
    execution=dict(seconds=e['seconds'],exit_code=0,stop_reason=None,
        peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in e['resource_samples']),
        minimum_sampled_free_bytes=min(s['free_bytes'] for s in e['resource_samples'])),
    pins={str(p):sha(p) for p in [Path(__file__),H/'scripts/rational_basis.py',H/'scripts/run_rational.py',H/'data/rational-execution.json',H/'data/rational-summary.json',H/'data/square-audit.json']})
for p,h in frozen.items():assert sha(H/p)==h
(H/'data/rational-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
