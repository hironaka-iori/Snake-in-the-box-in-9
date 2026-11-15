"""Read-only exact audit of the three certificates closing the stage-one leaf."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from copy import deepcopy
import ast, hashlib, json
H=Path(__file__).resolve().parents[1]; R=H.parents[1]; P=R/'milestones/221-square-parity'
def read(p):return json.loads(Path(p).read_bytes())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q):return [q.numerator,q.denominator]
def key(path):return '-'.join(map(str,path))
def fraction(p):
    assert len(p)==2 and all(type(v) is int for v in p) and p[1]>0
    q=Q(*p);assert rat(q)==p
    return q
pins={}
def pin(path,expected=None):
    path=Path(path);h=sha(path)
    if expected is not None:assert h==expected,str(path)
    pins[str(path)]=h
    return h
frozen={
 'scripts/audit_prefix.py':'18233a04e77650df97841a5736bb0abe5dafa132fe04c3f55586890e3c410bcb',
 'data/prefix-audit.json':'8a070ed47d2d6192ab371ed3b96c78fd24763c89417ae83b95477af97209d2b6',
 'logs/prefix-review.md':'0a51b3678cb9cf3c03c87b96d0d490db2ffd6087080794b64cbb0766084bf5bd',
 'data/prefix-ledger.json':'59b4f6b316b7c5713c87810412198ecae00f010cd1e9f5fdafa5471093129d50',
 'data/continuation-ledger.json':'323d5c00de98df6bdfdcd03e23ba1692acf98c15ee6e8d45aa125804ac9f3253'}
for p,h in frozen.items():pin(H/p,h)
prior=read(H/'data/prefix-audit.json')
assert prior['status']=='PASS_EXACT_STAGE1_PREFIX_COVERAGE_AND_CERTIFICATES'
for p,h in prior['pins'].items():pin(R/p,h)
initial=read(H/'data/continuation-ledger.json');final=read(H/'data/deep-ledger.json');summary=read(H/'data/deep-summary.json')
pin(H/'data/deep-ledger.json','58c66c01369e5108a6b411268668d70a078d2e2b83cf41a1bbb631e65248a0c8')
maps=[]
for p in [H/'scripts/prefix_search.py',H/'scripts/prefix_deep.py']:
    tree=ast.parse(p.read_text(encoding='utf-8'))
    maps.append({n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,ast.FunctionDef)})
for name in ('key','candidates','solve'):assert maps[0][name]==maps[1][name]
models={t:read(P/'data'/f'long-{t}/model.json') for t in (0,78)}
names={t:{n:i for i,n in enumerate(m['variables'])} for t,m in models.items()}
N={t:{u:sorted(v for v in m['vertices'] if (u^v).bit_count()==1) for u in m['vertices']} for t,m in models.items()}
for root,m in models.items():
    assert sorted((u,v) for u in N[root] for v in N[root][u] if u<v)==[tuple(e) for e in m['edges']]
def candidates(path):
    assert 1<=len(path)-1<=8<93 and len(path)==len(set(path))
    assert all(v in N[path[0]] for v in path)
    assert all((u^v).bit_count()==1 for u,v in zip(path,path[1:]))
    assert all((path[i]^path[j]).bit_count()!=1 for i in range(len(path)) for j in range(i+2,len(path)))
    return [v for v in N[path[0]][path[-1]] if v not in path and all((v^u).bit_count()!=1 for u in path[:-1])]
ledger=deepcopy(initial);ledger['maximum_prefix_edges']=8
assert ledger['jobs']==74 and ledger['queue']==[]
pending=[(k,n) for k,n in ledger['nodes'].items() if n['status']=='PENDING_DEPTH_LIMIT'];assert len(pending)==1
oldkey,node=pending[0]
assert node['prefix']==[78,206,198,196,197] and candidates(node['prefix'])==[213]
def expand(k,node):
    children=candidates(node['prefix']);assert children
    node.update(status='EXPANDED',next_vertices=children,children=[key(node['prefix']+[v]) for v in children])
    for v,c in zip(children,node['children']):
        assert c not in ledger['nodes']
        ledger['nodes'][c]=dict(prefix=node['prefix']+[v],parent=k,status='PENDING');ledger['queue'].append(c)
expand(oldkey,node)
records=[json.loads(s) for s in (H/'logs/deep-stdout.log').read_text(encoding='utf-8').splitlines()]
assert len(records)==4 and records[-1]==summary
certificates=[]
for record in records[:-1]:
    k=ledger['queue'].pop(0);node=ledger['nodes'][k];path=node['prefix']
    assert record['prefix']==path and node['status']=='PENDING' and candidates(path)
    m,n=models[path[0]],names[path[0]]
    file=H/'data/deep-cases'/(k+'.json');c=read(file);h=pin(file)
    assert c['root']==path[0] and c['prefix']==path
    assert c['base_model_sha256']==pin(P/'data'/f'long-{path[0]}/model.json')
    assert c['source_sha256']==pin(H/'scripts/prefix_deep.py')
    added=[dict(name=f'prefix_x_{v}',terms=[[n[f'x{v}'],1]],sense='eq',rhs=1) for v in path[1:]]
    added += [dict(name=f'prefix_nonendpoint_{v}',terms=[[n[f'e{v}'],1]],sense='eq',rhs=0) for v in path[1:] if f'e{v}' in n]
    assert c['appended_rows']==added and c['status']=='EXACT_UPPER_CERTIFICATE' and c['native_status_code']==0
    rows=m['rows']+added;assert c['row_count']==len(rows)
    D=c['scale'];assert type(D) is int and D==10**6
    sparse=c['nonzero_weights']
    assert all(len(p)==2 and all(type(v) is int for v in p) for p in sparse)
    assert [i for i,w in sparse]==sorted({i for i,w in sparse})
    weights=[0]*len(rows)
    for i,w in sparse:
        assert 0<=i<len(rows) and w!=0
        assert rows[i]['sense']=='eq' or (rows[i]['sense']=='le' and w>0)
        weights[i]=w
    residual=[D*a for a in m['objective']];rhs=0
    for row,w in zip(rows,weights):
        rhs+=w*row['rhs']
        for i,a in row['terms']:residual[i]-=w*a
    assert len(residual)==574 and residual==c['residual']
    numerator=rhs+sum(max(v,0) for v in residual);assert numerator==c['upper_numerator']
    bound=Q(numerator,D);assert rat(bound)==c['upper_bound']
    ledger['jobs']+=1
    node.update(certificate=str(file.relative_to(R)),sha256=h,upper_bound=rat(bound))
    if bound<94:node['status']='EXCLUDED_BOUND'
    else:
        assert len(path)-1<8
        expand(k,node)
    assert record==dict(prefix=path,status=node['status'],upper_bound=rat(bound),jobs=ledger['jobs'],queue=len(ledger['queue']))
    certificates.append(dict(prefix=path,appended_rows=len(added),nonzero_weights=len(sparse),weighted_rhs=rhs,
        positive_residual_sum=sum(max(v,0) for v in residual),exact_upper=rat(bound),excludes_93_edges=bound<94,
        sha256=h,file=str(file.relative_to(H))))
assert sorted(p.name for p in (H/'data/deep-cases').glob('*.json'))==sorted(key(c['prefix'])+'.json' for c in certificates)
assert not ledger['queue'] and ledger['jobs']==77
ledger['stop_reason']='QUEUE_FINISHED';ledger['seconds']=summary['seconds'];assert ledger==final
assert (json.dumps(ledger,indent=2)+'\n').replace('\n','\r\n').encode('utf-8')==(H/'data/deep-ledger.json').read_bytes()
assert all(final['nodes'][k]==n for k,n in initial['nodes'].items() if k!=oldkey)
old=dict(final['nodes'][oldkey]);old['status']='PENDING_DEPTH_LIMIT';old.pop('children');old.pop('next_vertices')
assert old==initial['nodes'][oldkey]
assert set(final['nodes'])-set(initial['nodes'])=={key(c['prefix']) for c in certificates}
assert [c['exact_upper'] for c in certificates]==[[1183031,12500],[3759179,40000],[46707409,500000]]
# Entire tree coverage is checked again; inherited certificate arithmetic remains frozen.
nodes=final['nodes'];childkeys=[]
for k,node in nodes.items():
    path=node['prefix'];assert key(path)==k;allowed_next=candidates(path)
    if node['status']=='EXPANDED':
        assert node['next_vertices']==allowed_next and allowed_next
        assert node['children']==[key(path+[v]) for v in allowed_next];childkeys.extend(node['children'])
    else:
        assert node['status'] in ('EXCLUDED_BOUND','EXCLUDED_INHERITED')
        assert fraction(node['upper_bound'])<94 and 'children' not in node
    if len(path)>2:assert node['parent']==key(path[:-1]) and k in nodes[node['parent']]['children']
    else:assert 'parent' not in node
assert len(childkeys)==len(set(childkeys))==66
assert set(childkeys)=={k for k,n in nodes.items() if len(n['prefix'])>2}
assert sorted(tuple(n['prefix']) for n in nodes.values() if len(n['prefix'])==2)==[(t,v) for t in (0,78) for v in N[t][t]]
counts=dict(sorted(Counter(n['status'] for n in nodes.values()).items()))
assert len(nodes)==80 and counts=={'EXCLUDED_BOUND':50,'EXCLUDED_INHERITED':3,'EXPANDED':27}
assert all(not n['status'].startswith('PENDING') for n in nodes.values())
depths={str(d):{s:sum(n['status']==s and len(n['prefix'])-1==d for n in nodes.values()) for s in counts} for d in range(1,9)}
assert summary==dict(jobs=77,nodes=80,counts=counts,stop_reason='QUEUE_FINISHED',seconds=ledger['seconds'],ledger_sha256=sha(H/'data/deep-ledger.json'),by_depth=depths)
root_reports=[]
for root,expected_nodes,expected_leaves,expected_upper in [(0,46,31,Q(9396307,100000)),(78,34,22,Q(93984077,10**6))]:
    rn=[n for n in nodes.values() if n['prefix'][0]==root]
    leaves=[n for n in rn if n['status']!='EXPANDED']
    upper=max(fraction(n['upper_bound']) for n in leaves)
    assert len(rn)==expected_nodes and len(leaves)==expected_leaves and upper==expected_upper<94
    root_reports.append(dict(root=root,nodes=len(rn),excluded_leaves=len(leaves),maximum_leaf_upper=rat(upper),
        margin_below94=rat(94-upper),maximizing_prefixes=[n['prefix'] for n in leaves if fraction(n['upper_bound'])==upper]))
e=read(H/'data/deep-execution.json')
assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
for p,h in e['pins'].items():pin(H/p,h)
for stream in ('stdout','stderr'):pin(H/f'logs/deep-{stream}.log',e[f'{stream}_sha256'])
pin(H/'data/deep-summary.json',e['summary_sha256'])
gate=e['resource_gate'];assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
for s in e['resource_samples']:
    assert not s['errors'] and not s['lean_processes'] and s['free_bytes']>=768*1024**2
    assert s['private_bytes'] is None or s['private_bytes']<=256*1024**2
assert e['thread_environment']=={k:'1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
# Generic Lean receipt identity only; no compiler is invoked.
lean=read(H/'data/Prefix222-audit.json')
assert lean['status']=='PASS' and lean['exit_code']==0 and lean['stop_reason'] is None
pin(lean['source'],lean['source_sha256']);pin(lean['object'],lean['olean_sha256']);pin(lean['log'],lean['log_sha256'])
assert [a['theorem'] for a in lean['axioms']]==['Prefix222.prefix_next','Prefix222.prefix_nonroot_not_endpoints','Prefix222.prefix_free_endpoint_zero']
assert all(a['axioms']==['propext','Quot.sound'] for a in lean['axioms'])
log=Path(lean['log']).read_text(encoding='utf-8')
assert all(a['theorem'] in log for a in lean['axioms']) and 'sorryAx' not in log
for p in [Path(__file__),H/'scripts/prepare_deep.py',H/'data/deep-execution.json',H/'data/Prefix222-audit.json']:pin(p)
for p,h in frozen.items():assert sha(H/p)==h
report=dict(status='PASS_EXACT_COMPLETE_FIXED_ROOT_PREFIX_EXCLUSION',
 scope='Independent saved-data arithmetic and complete child coverage. Three new certificates checked, frozen stage1 receipt and all its pins reused. No optimizer, compiler, search, software tests, or numerical primal assumptions.',
 initial=dict(nodes=77,queries=74,unique_pending_prefix=initial['nodes'][oldkey]['prefix'],prior_ledger_sha256=frozen['data/continuation-ledger.json']),
 continuation=dict(new_queries=3,cumulative_queries=77,total_nodes=80,counts=counts,unresolved_leaves=0,unchanged_inherited_nodes=76,
   only_inherited_change='The unique depth4 pending leaf becomes EXPANDED; its original certificate and all other fields are retained.',
   forced_next=213,following_choices=[215,221],all_child_sets_recomputed=True,byte_exact_final_ledger=True),
 certificates=certificates,root_results=root_reports,
 conclusion='Within the frozen allowed graphs at roots0 and78 of the saved98-edge parent, every possible93-edge induced path is excluded. Any longer partner would have such a prefix; hence each arbitrary partner has at most92 edges and a one-crossing join with this parent at most98+1+92=191 edges. Global bounds are unchanged.',
 actual_path_scope='Uses the previously reviewed necessity of the fixed-parent model rows, proper-prefix selection and nonendpoint facts, and the complete finite branching cover. No Boolean witness or exclusion for other parents or different join constructions is asserted.',
 lean_scope=dict(generic_receipt_status='PASS',theorems=lean['axioms'],source_log_object_hashes_checked=True,
   limitation='Generic Prefix222 results remain separate from an end-to-end Lean assembly of the concrete prefix tree and weighted certificates. No independent compiler run performed.'),
 execution=dict(status=e['status'],exit_code=0,stop_reason=None,seconds=e['seconds'],
   peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in e['resource_samples']),minimum_sampled_free_bytes=min(s['free_bytes'] for s in e['resource_samples'])),pins=pins)
(H/'data/deep-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:report[k] for k in ('status','continuation','certificates','root_results','execution')},indent=2))
