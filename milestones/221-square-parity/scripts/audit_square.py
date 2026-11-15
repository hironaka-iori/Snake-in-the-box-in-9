"""Exact saved-record audit of square parity rows and their certificates."""
from pathlib import Path
from fractions import Fraction as Q
from math import isfinite
import hashlib
import json

H=Path(__file__).resolve().parents[1]
P=H.parent/'220-subset-forest'
def read(p):return json.loads(Path(p).read_bytes())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q):return [q.numerator,q.denominator]
def fraction(p):
    assert len(p)==2 and all(type(v) is int for v in p) and p[1]>0
    q=Q(*p);assert rat(q)==p
    return q
def upper_check(m,c):
    D=c['scale'];assert type(D) is int and D==10**6
    assert len(c['weights'])==len(m['rows'])
    residual=[D*v for v in m['objective']];rhs=0
    for row,w in zip(m['rows'],c['weights']):
        assert type(w) is int and (row['sense']=='eq' or w>=0)
        rhs+=w*row['rhs']
        for i,a in row['terms']:residual[i]-=w*a
    positive=[max(v,0) for v in residual];numerator=rhs+sum(positive)
    assert c['residual']==residual and c['positive_residual']==positive
    assert c['upper_numerator']==numerator and fraction(c['upper_bound'])==Q(numerator,D)
    return Q(numerator,D)
def execution(kind):
    e=read(H/f'data/{kind}-execution.json')
    assert e['status']=='ACCEPTED_NATIVE_RESULT' and e['exit_code']==0 and e['stop_reason'] is None
    for p,h in e['pins'].items():assert sha(H/p)==h
    for stream in ('stdout','stderr'):assert sha(H/f'logs/{kind}-{stream}.log')==e[f'{stream}_sha256']
    assert sha(H/f'data/{kind}-summary.json')==e['summary_sha256']
    assert e['thread_environment']=={k:'1' for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
    gate=e['resource_gate'];assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
    for s in e['resource_samples']:
        assert not s['errors'] and not s['lean_processes'] and s['free_bytes']>=768*1024**2
        assert s['private_bytes'] is None or s['private_bytes']<=256*1024**2
    return dict(seconds=e['seconds'],exit_code=0,stop_reason=None,
        peak_sampled_private_bytes=max(s['private_bytes'] or 0 for s in e['resource_samples']),
        minimum_sampled_free_bytes=min(s['free_bytes'] for s in e['resource_samples']),
        execution_sha256=sha(H/f'data/{kind}-execution.json'),summary_sha256=e['summary_sha256'])

assert sha(P/'data/forest-audit.json')=='57ace9b15ef58fccaa716bf7c3167b39dd842c5f44f148fcc625c3e22c51ffad'
prior=read(P/'data/forest-audit.json')
assert prior['status']=='PASS_EXACT_SUBSET_ROWS_UPPERS_PRIMALS_CYCLES_FLOWS_AND_TARGET94'
for p,h in prior['pins'].items():assert sha(P/p)==h
run=execution('square');summary=read(H/'data/square-summary.json')
assert [s['root'] for s in summary]==[0,78]
reports=[]
for root in (0,78):
    F=H/'data'/f'square-{root}';basefile=P/'data'/f'forest-{root}'/'model.json'
    b=read(basefile);m=read(F/'model.json');native=read(F/'native-result.json');cert=read(F/'upper-certificate.json')
    old=next(s for s in prior['models'] if s['root']==root)
    assert sha(basefile)==old['pins'][f'data\\forest-{root}\\model.json']==m['base_model_sha256']
    for key in ('root','form','variables','lower','upper','objective','vertices','edges','cycles','source_sha256','source_sha256_220','seed_sha256','graph_sha256'):
        assert m[key]==b[key],key
    assert m['source_sha256_221']==sha(H/'scripts/square_separation.py')
    assert m['rows'][:len(b['rows'])]==b['rows']
    inherited=b['subset_witnesses'];assert m['subset_witnesses'][:len(inherited)]==inherited
    V=m['vertices'];S=set(V);edges={tuple(e) for e in m['edges']};names={n:i for i,n in enumerate(m['variables'])}
    # Enumerate every coordinate face of dimension two directly in the allowed Q8 graph.
    squares=set()
    for v in V:
        for i in range(8):
            for j in range(i+1,8):
                C=frozenset((v,v^(1<<i),v^(1<<j),v^(1<<i)^(1<<j)))
                if C<=S:squares.add(C)
    initial_squares=[frozenset(c) for c in b['cycles'] if len(c)==4]
    assert len(initial_squares)==len(set(initial_squares)) and set(initial_squares)==squares
    assert len(squares)==(156 if root==0 else 154)
    sw=m['square_witnesses'];assert len(sw)==8*len(squares)
    seen={};expected_square_rows=[]
    for k,w in enumerate(sw):
        cycle=w['cycle'];C=frozenset(cycle);odd=w['odd_edge_indices']
        assert C in squares and len(cycle)==len(C)==4 and cycle[0]==min(C)
        ce=[tuple(sorted((cycle[i],cycle[(i+1)%4]))) for i in range(4)]
        assert len(set(ce))==4 and all(e in edges for e in ce)
        assert odd==sorted(set(odd)) and set(odd)<=set(range(4)) and len(odd) in (1,3)
        seen.setdefault(C,set());mask=sum(1<<i for i in odd);assert mask not in seen[C];seen[C].add(mask)
        terms={}
        for i,(u,v) in enumerate(ce):
            sign=1 if i in odd else -1
            for name,a in ((f'x{u}',sign),(f'x{v}',sign),(f'y{u}_{v}',-2*sign)):
                index=names[name];terms[index]=terms.get(index,0)+a
        row=dict(name=f'square_parity_{k}',terms=[[i,a] for i,a in sorted(terms.items()) if a],sense='le',rhs=len(odd)-1)
        assert w['row_index']==len(b['rows'])+k and m['rows'][w['row_index']]==row
        expected_square_rows.append(row)
    assert set(seen)==squares and all(masks=={i for i in range(16) if i.bit_count()%2} for masks in seen.values())
    added=m['subset_witnesses'][len(inherited):];assert len(added)==(0 if root==0 else 4)
    keys={(w['vertex'],tuple(w['subset'])) for w in inherited}
    for k,w in enumerate(added):
        U=w['subset'];v=w['vertex'];subset=set(U)
        assert U==sorted(subset) and subset<=S and v in subset
        key=(v,tuple(U));assert key not in keys;keys.add(key)
        terms={names[f'x{u}']:-1 for u in U};terms[names[f'x{v}']]+=1
        for u,t in m['edges']:
            if u in subset and t in subset:terms[names[f'y{u}_{t}']]=1
        row=dict(name=f'forest221_{k}',terms=[[i,a] for i,a in sorted(terms.items()) if a],sense='le',rhs=0)
        assert w['row_index']==len(b['rows'])+len(sw)+k and m['rows'][w['row_index']]==row
        assert type(w['iteration']) is int and w['iteration']>=0 and isfinite(w['violation_at_discovery']) and w['violation_at_discovery']>1e-7
    assert len(m['rows'])==len(b['rows'])+len(sw)+len(added)
    assert native['model_sha256']==cert['model_sha256']==sha(F/'model.json')
    assert native['status']=='OPTIMAL_NATIVE' and native['added_square_rows']==len(sw) and native['added_subset_count']==len(added)
    assert len(native['values'])==574 and len(native['duals'])==len(m['rows'])
    assert all(isfinite(v) for v in native['values']+native['duals'])
    bound=upper_check(m,cert);assert bound==fraction(native['exact_upper'])
    assert cert['weights']==[max(0,round(w*10**6)) if row['sense']=='le' else round(w*10**6) for row,w in zip(m['rows'],native['duals'])]
    assert next(s for s in summary if s['root']==root)=={k:v for k,v in native.items() if k not in ('values','duals','steps')}
    steps=native['steps'];assert [s['iteration'] for s in steps]==list(range(len(steps)))
    for s in steps:
        assert s['rows']==len(b['rows'])+len(sw)+sum(w['iteration']<s['iteration'] for w in added)
        if s['iteration']<60:assert s['new_violated_subsets']==sum(w['iteration']==s['iteration'] for w in added)
    assert steps[-1]['new_violated_subsets']==0 and native['no_new_violations_at_tolerance'] is True
    old_violations=[]
    for label in ('primal','target94'):
        oldfile=P/'data'/f'rational-{root}'/(label+'-certificate.json')
        assert sha(oldfile)==old['pins'][f'data\\rational-{root}\\{oldfile.name}']
        values=[fraction(v) for v in read(oldfile)['values']]
        violations=[(i,sum((a*values[j] for j,a in row['terms']),Q())-row['rhs']) for i,row in enumerate(expected_square_rows)]
        positive=[(i,q) for i,q in violations if q>0]
        old_violations.append(dict(point=label,violating_square_rows=len(positive),largest_violation=rat(max((q for _,q in positive),default=Q())),
            largest_row_index=(len(b['rows'])+max(positive,key=lambda t:t[1])[0]) if positive else None))
    reports.append(dict(root=root,base_rows=len(b['rows']),coordinate_squares=len(squares),square_parity_rows=len(sw),
        new_subset_rows=len(added),total_rows=len(m['rows']),variables=574,exact_upper=rat(bound),
        numerical_objective_not_exact_optimality=native['objective'],upper_below94=bound<94,
        old220_square_violations=old_violations,
        pins={str(p.relative_to(H)):sha(p) for p in F.iterdir() if p.is_file()}))
report=dict(status='PASS_EXACT_SQUARE_SUBSET_ROWS_AND_UPPER_CERTIFICATES',
    scope='All coordinate squares enumerated from frozen allowed cube vertices; all eight odd-subset rows per square reconstructed; inherited rows and new subset rows checked; exact residual certificates recomputed. No optimizer, compiler, search, or software tests.',
    models=reports,execution=run,
    rational_status='Not included in this baseline audit; requires separately confirmed terminal records.',
    reviewer_repair='First audit reached report serialization after substantive checks, then failed because a predecessor file is outside this milestone. Pin keys now use absolute paths; no producer evidence changed.',
    pins={str(p):sha(p) for p in [Path(__file__),H/'scripts/prepare_square.py',H/'scripts/square_separation.py',H/'scripts/run_square.py',P/'data/forest-audit.json']})
(H/'data/square-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
