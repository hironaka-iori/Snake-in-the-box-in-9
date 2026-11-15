"""Independent exact audit of the saved first prefix ledger and its continuation."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from copy import deepcopy
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R / 'milestones/221-square-parity'

def read(p):
    return json.loads(Path(p).read_bytes())

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def rat(q):
    return [q.numerator, q.denominator]

def fraction(p):
    assert len(p) == 2 and all(type(v) is int for v in p) and p[1] > 0
    q = Q(*p)
    assert rat(q) == p
    return q

def key(path):
    return '-'.join(map(str, path))

def serialized(obj):
    # The producer uses Path.write_text with Windows newline translation.
    return (json.dumps(obj, indent=2)+'\n').replace('\n','\r\n').encode('utf-8')

pins = {}
def pin(path, expected=None):
    path = Path(path)
    h = sha(path)
    if expected is not None:
        assert h == expected, str(path)
    pins[str(path.relative_to(R))] = h
    return h

first_audit_hash = '84283463d10dc79cc5e375ac1968c562b3e38c47a1a29f5ced842c4ac52b8562'
initial_hash = '59b4f6b316b7c5713c87810412198ecae00f010cd1e9f5fdafa5471093129d50'
final_hash = '323d5c00de98df6bdfdcd03e23ba1692acf98c15ee6e8d45aa125804ac9f3253'
pin(P/'data/first-audit.json', first_audit_hash)
first_audit = read(P/'data/first-audit.json')
assert first_audit['status'] == 'PASS_EXACT_FIRST_STEP_COVERAGE_AND_UPPER_CERTIFICATES'
for p, h in first_audit['pins'].items():
    pin(P/p, h)
first = read(P/'data/first-summary.json')
models = {root: read(P/'data'/f'long-{root}/model.json') for root in (0,78)}
model_hashes = {root: pin(P/'data'/f'long-{root}/model.json') for root in models}
names = {root: {n:i for i,n in enumerate(m['variables'])} for root,m in models.items()}
neighbours = {}
for root,m in models.items():
    assert len(m['vertices']) == len(set(m['vertices'])) == 158
    assert len(m['variables']) == len(names[root]) == 574
    assert m['lower'] == [0]*574 and m['upper'] == [1]*574
    assert m['objective'] == [1]*158+[0]*416
    N = {u: sorted(v for v in m['vertices'] if (u^v).bit_count() == 1) for u in m['vertices']}
    literal_edges = sorted((u,v) for u in N for v in N[u] if u<v)
    assert literal_edges == [tuple(e) for e in m['edges']]
    neighbours[root] = N
expected_first = [(root,v) for root in (0,78) for v in neighbours[root][root]]
assert [(b['root'],b['first_vertex']) for b in first] == expected_first
assert len(first) == 14

def candidates(path):
    assert len(path) == len(set(path))
    assert 1 <= len(path)-1 <= 4 < 93
    assert all(v in neighbours[path[0]] for v in path)
    assert all((u^v).bit_count() == 1 for u,v in zip(path,path[1:]))
    assert all((path[i]^path[j]).bit_count() != 1
               for i in range(len(path)) for j in range(i+2,len(path)))
    return [v for v in neighbours[path[0]][path[-1]]
            if v not in path and all((v^u).bit_count() != 1 for u in path[:-1])]

certificates = []
def check_certificate(file, path, inherited=False, source=None):
    c = read(file)
    root = path[0]
    m, n = models[root], names[root]
    h = pin(file)
    assert c['root'] == root and c['base_model_sha256'] == model_hashes[root]
    if inherited:
        assert len(path) == 2 and c['first_vertex'] == path[1]
        added = [dict(name='fixed_first_vertex',terms=[[n[f'x{path[1]}'],1]],sense='eq',rhs=1)]
        assert c['appended_row'] == added[0]
        assert c['status'] == 'OPTIMAL_NATIVE'
        source = P/'scripts/first_step.py'
    else:
        assert c['prefix'] == path and c['status'] == 'EXACT_UPPER_CERTIFICATE'
        added = [dict(name=f'prefix_x_{v}',terms=[[n[f'x{v}'],1]],sense='eq',rhs=1) for v in path[1:]]
        added += [dict(name=f'prefix_nonendpoint_{v}',terms=[[n[f'e{v}'],1]],sense='eq',rhs=0)
                  for v in path[1:] if f'e{v}' in n]
        assert c['appended_rows'] == added
        assert c['native_status_code'] == 0
    assert c['source_sha256'] == pin(source)
    rows = m['rows']+added
    if 'row_count' in c:
        assert c['row_count'] == len(rows)
    scale = c['scale']
    assert type(scale) is int and scale == 10**6
    sparse = c['nonzero_weights']
    assert all(len(pair) == 2 and all(type(v) is int for v in pair) for pair in sparse)
    assert [i for i,w in sparse] == sorted({i for i,w in sparse})
    weights = [0]*len(rows)
    for i,w in sparse:
        assert 0 <= i < len(rows) and w != 0
        assert rows[i]['sense'] == 'eq' or (rows[i]['sense'] == 'le' and w > 0)
        weights[i] = w
    residual = [scale*a for a in m['objective']]
    rhs = 0
    for row,w in zip(rows,weights):
        rhs += row['rhs']*w
        for i,a in row['terms']:
            residual[i] -= a*w
    assert residual == c['residual'] and len(residual) == 574
    numerator = rhs+sum(max(v,0) for v in residual)
    assert type(c['upper_numerator']) is int and c['upper_numerator'] == numerator
    bound = Q(numerator,scale)
    assert bound == fraction(c['upper_bound'])
    certificates.append(dict(prefix=path,inherited=inherited,rows=len(rows),appended_rows=len(added),
        endpoint_zero_rows=sum(row['name'].startswith('prefix_nonendpoint_') for row in added),
        nonzero_weights=len(sparse),weighted_rhs=rhs,positive_residual_sum=sum(max(v,0) for v in residual),
        exact_upper=rat(bound),excludes_93_edges=bound<94,
        file=str(file.relative_to(R)),sha256=h))
    return c, h, bound

def execution(kind, interrupted=False):
    p = H/f'data/{kind}-execution.json'
    e = read(p)
    pin(p)
    for rel,h in e['pins'].items():
        pin(H/rel,h)
    for stream in ('stdout','stderr'):
        pin(H/f'logs/{kind}-{stream}.log',e[f'{stream}_sha256'])
    assert e['thread_environment'] == {k:'1' for k in
        ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
    gate=e['resource_gate']
    assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
    samples=e['resource_samples']
    assert all(not s['errors'] and not s['lean_processes'] for s in samples)
    assert all(s['private_bytes'] is None or s['private_bytes']<=256*1024**2 for s in samples)
    if interrupted:
        assert e['status']=='INTERRUPTED' and e['stop_reason']=='LOW_FREE_MEMORY' and e['exit_code']==1
        assert samples[-1]['free_bytes'] < 768*1024**2
        assert all(s['free_bytes']>=768*1024**2 for s in samples[:-1])
        assert 'summary_sha256' not in e and not (H/'data/prefix-summary.json').exists()
    else:
        assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['stop_reason'] is None and e['exit_code']==0
        assert all(s['free_bytes']>=768*1024**2 for s in samples)
        pin(H/f'data/{kind}-summary.json',e['summary_sha256'])
    return dict(status=e['status'],exit_code=e['exit_code'],stop_reason=e['stop_reason'],seconds=e['seconds'],
        peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in samples),
        minimum_sampled_free_bytes=min(s['free_bytes'] for s in samples))

executions={'prefix':execution('prefix',True),'continuation':execution('continuation')}
initial_file=H/'data/prefix-ledger.json'
final_file=H/'data/continuation-ledger.json'
pin(initial_file,initial_hash)
pin(final_file,final_hash)
initial, final = read(initial_file), read(final_file)
input_record=read(H/'data/continuation-input.json')
assert input_record['initial_ledger_sha256']==initial_hash and input_record['initial_jobs']==45
pin(H/'data/continuation-input.json')
input_paths=[P/'data/first-summary.json',P/'data/first-audit.json',P/'data/long-0/model.json',P/'data/long-78/model.json']
ledger=dict(target_edges=93,maximum_prefix_edges=4,maximum_jobs=400,nodes={},queue=[],jobs=0,
            input_pins={str(p.relative_to(R)):sha(p) for p in input_paths})
for b in first:
    path=[b['root'],b['first_vertex']]
    k=key(path)
    candidates(path)
    if fraction(b['upper_bound'])<94:
        file=P/'data'/f'first-{path[0]}'/f'vertex-{path[1]}.json'
        c,h,bound=check_certificate(file,path,True)
        branch=next(x for x in first_audit['branches'] if x['root']==path[0] and x['first_vertex']==path[1])
        assert h==b['sha256']==branch['sha256'] and rat(bound)==b['upper_bound']==branch['exact_upper']
        ledger['nodes'][k]=dict(prefix=path,status='EXCLUDED_INHERITED',certificate=str(file.relative_to(R)),sha256=h,upper_bound=rat(bound))
    else:
        ledger['nodes'][k]=dict(prefix=path,status='PENDING')
        ledger['queue'].append(k)
assert len(ledger['queue'])==11

def replay_records(records, stage):
    folder='cases' if stage=='prefix' else 'continuation-cases'
    source=H/'scripts'/('prefix_search.py' if stage=='prefix' else 'prefix_continue.py')
    used=[]
    for record in records:
        assert ledger['queue']
        k=ledger['queue'].pop(0)
        node=ledger['nodes'][k]
        assert node['status']=='PENDING' and record['prefix']==node['prefix']
        path=node['prefix']
        next_vertices=candidates(path)
        assert next_vertices  # These frozen records contain no no-next exclusions.
        file=H/'data'/folder/(k+'.json')
        c,h,bound=check_certificate(file,path,source=source)
        used.append(file.name)
        ledger['jobs']+=1
        node.update(certificate=str(file.relative_to(R)),sha256=h,upper_bound=rat(bound))
        if bound<94:
            node['status']='EXCLUDED_BOUND'
        elif len(path)-1==4:
            node['status']='PENDING_DEPTH_LIMIT'
        else:
            node['status']='EXPANDED'
            node['next_vertices']=next_vertices
            node['children']=[key(path+[v]) for v in next_vertices]
            for v,child in zip(next_vertices,node['children']):
                assert child not in ledger['nodes']
                ledger['nodes'][child]=dict(prefix=path+[v],parent=k,status='PENDING')
                ledger['queue'].append(child)
        assert record==dict(prefix=path,status=node['status'],upper_bound=rat(bound),jobs=ledger['jobs'],queue=len(ledger['queue']))
    assert sorted(used)==sorted(p.name for p in (H/'data'/folder).glob('*.json'))
    return used

initial_lines=[json.loads(s) for s in (H/'logs/prefix-stdout.log').read_text(encoding='utf-8').splitlines()]
assert len(initial_lines)==45
replay_records(initial_lines,'prefix')
assert ledger==initial and serialized(ledger)==initial_file.read_bytes()
assert ledger['jobs']==45 and len(ledger['queue'])==20 and len(ledger['nodes'])==68
assert {k for k,n in ledger['nodes'].items() if n['status']=='PENDING'}==set(ledger['queue'])
initial_completed={k:deepcopy(n) for k,n in ledger['nodes'].items() if n['status']!='PENDING'}
initial_queue=list(ledger['queue'])

continuation_lines=[json.loads(s) for s in (H/'logs/continuation-stdout.log').read_text(encoding='utf-8').splitlines()]
summary=read(H/'data/continuation-summary.json')
assert continuation_lines[-1]==summary and len(continuation_lines[:-1])==29
replay_records(continuation_lines[:-1],'continuation')
assert not ledger['queue'] and ledger['jobs']==74
ledger['stop_reason']='QUEUE_FINISHED'
ledger['seconds']=summary['seconds']
assert ledger==final and serialized(ledger)==final_file.read_bytes()
assert all(ledger['nodes'][k]==n for k,n in initial_completed.items())
assert all(ledger['nodes'][k]['status']!='PENDING' for k in initial_queue)

nodes=ledger['nodes']
counts=dict(sorted(Counter(n['status'] for n in nodes.values()).items()))
assert counts=={'EXCLUDED_BOUND':48,'EXCLUDED_INHERITED':3,'EXPANDED':25,'PENDING_DEPTH_LIMIT':1}
depths={str(d):{s:sum(n['status']==s and len(n['prefix'])-1==d for n in nodes.values()) for s in counts} for d in range(1,5)}
expected_summary=dict(jobs=74,nodes=len(nodes),counts=counts,stop_reason='QUEUE_FINISHED',seconds=ledger['seconds'],ledger_sha256=sha(final_file),by_depth=depths)
assert summary==expected_summary and len(nodes)==77
# Audit the finite tree independently of queue reconstruction: unique parent and complete children.
children=[]
for k,node in nodes.items():
    path=node['prefix']
    assert k==key(path)
    cv=candidates(path)
    if len(path)==2:
        assert 'parent' not in node and tuple(path) in expected_first
    else:
        assert node['parent']==key(path[:-1]) and k in nodes[node['parent']]['children']
    if node['status']=='EXPANDED':
        assert len(path)-1<4 and node['next_vertices']==cv
        assert node['children']==[key(path+[v]) for v in cv]
        children.extend(node['children'])
    else:
        assert 'children' not in node
assert len(children)==len(set(children))==63
assert set(children)=={k for k,n in nodes.items() if len(n['prefix'])>2}
leaves=[n for n in nodes.values() if n['status'].startswith('PENDING')]
assert len(leaves)==1 and leaves[0]['prefix']==[78,206,198,196,197]
assert fraction(leaves[0]['upper_bound'])==Q(47321233,500000)
assert all(n['status'] in ('EXCLUDED_BOUND','EXCLUDED_INHERITED','EXPANDED')
           for n in nodes.values() if n['prefix'][0]==0)
assert len(certificates)==77 and sum(not c['inherited'] for c in certificates)==74
assert sum(c['excludes_93_edges'] for c in certificates)==51
for file in [Path(__file__),H/'scripts/prepare_continuation.py',H/'scripts/prepare_round.py',H/'scripts/prepare_run.py',H/'scripts/run_prefix.py',H/'scripts/run_continuation.py']:
    pin(file)
assert sha(initial_file)==initial_hash and sha(final_file)==final_hash
report=dict(status='PASS_EXACT_STAGE1_PREFIX_COVERAGE_AND_CERTIFICATES',
    reviewer_repair='Initial semantic reconstruction passed, but the byte comparison assumed LF. It was corrected to the producer Windows CRLF serialization; no producer file changed.',
    scope='Saved-record audit only. Complete deterministic ledger reconstruction and independent cube-neighbour/induced-child enumeration; exact sparse weighted-row arithmetic. No optimizer, compiler, native search, software tests, or numerical primal/optimality assumptions.',
    interrupted_run=dict(jobs=45,nodes=68,completed_nodes_preserved=len(initial_completed),pending_queue=initial_queue,
        ledger_sha256=initial_hash,status='INTERRUPTED',stop_reason='LOW_FREE_MEMORY',no_successful_batch_claim=True),
    continuation=dict(new_queries=29,cumulative_queries=74,nodes=77,initial_pending_processed=20,
        further_nodes_created=9,counts=counts,by_depth=depths,ledger_sha256=final_hash,
        initial_ledger_byte_reconstruction=True,final_ledger_byte_reconstruction=True,
        inherited_completed_nodes_unchanged=True,no_omitted_or_duplicate_child_coverage=True),
    root_results=[dict(root=root,first_neighbours=neighbours[root][root],
        counts=dict(sorted(Counter(n['status'] for n in nodes.values() if n['prefix'][0]==root).items())),
        unresolved_prefixes=[n['prefix'] for n in leaves if n['prefix'][0]==root]) for root in (0,78)],
    surviving_leaf=dict(prefix=leaves[0]['prefix'],exact_upper=leaves[0]['upper_bound'],decimal='94.642466',
        limitation='This upper bound does not exclude cardinality94 and does not certify a feasible point or actual partner.'),
    endpoint_premise='For every nonroot proper-prefix position i<=k<93, injectivity gives p(i)!=p(93), so its free-endpoint indicator is zero. Odd prefix vertices have the appended e-variable equality; even vertices have no such variable.',
    coverage_argument='Every actual 93-edge path at either fixed root chooses one listed first neighbour; at each expanded proper prefix its next vertex is allowed, unused, adjacent only to the current prefix endpoint, hence is one of the enumerated children. All root0 leaves are excluded. Root78 is confined to the one listed depth4 prefix.',
    limits='The complete tree has one unresolved leaf. No complete two-root exclusion, actual partner, or global snake bound follows. The generic Prefix222 source and Lean receipts are separate from concrete certificate/coverage assembly; this audit makes no Lean completion claim.',
    certificates=certificates,executions=executions,pins=pins)
(H/'data/prefix-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:report[k] for k in ('status','interrupted_run','continuation','root_results','surviving_leaf','executions')},indent=2))
