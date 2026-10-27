"""Independent critical-graph, local-geometry, and full potential checks."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/52-share-on-235/scripts'))
from geometry_helpers import forest,shares
np=model.np
read=lambda p:json.loads((HERE/p).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
key=lambda ds,cs:min((model.canon(ds),tuple(cs)),(model.canon(ds[::-1]),tuple(cs[::-1])))
def decode(code):return tuple(code//6**k%6+1 for k in range(5,-1,-1))
source=ROOT/'milestones/55-critical-share-family/covered'
meta=json.loads((source/'data/model.json').read_text());analysis=json.loads((source/'data/analysis-share.json').read_text())
with np.load(source/'build/graph.npz') as z:base={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(base[k].tobytes())==h
raw=gzip.decompress((source/'data/potential-share.i64.gz').read_bytes());assert sha(raw)==analysis['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mean=Fraction(analysis['integer_weight_mean']);p,q=mean.numerator,mean.denominator
slack=q*(120*base['count'].astype(np.int64)+base['share_lower'])+pi[base['U']]-pi[base['V']]-p
assert np.all(slack>=0)
edges=read('data/critical-edges.json');windows=read('data/windows.json');nodes={e['u'] for e in edges}|{e['v'] for e in edges}
assert len(edges)==48 and len(nodes)==37 and len(windows)==17
for e in edges:
    i=e['source_edge'];assert base['U'][i]==e['u'] and base['V'][i]==e['v'] and slack[i]==0 and base['share_lower'][i]==0
    ds=meta['extensions'][int(base['direction'][i])][-6:];cs=decode(int(base['count_code'][i]))[-5:]
    row=windows[e['window']];assert key(ds,cs)==(tuple(row['directions']),tuple(row['counts']))
tight=np.flatnonzero(slack==0);adj=collections.defaultdict(list);rev=collections.defaultdict(list)
for u,v in zip(base['U'][tight].tolist(),base['V'][tight].tolist()):adj[u].append(v);rev[v].append(u)
def reach(graph,root):
    seen={root};stack=[root]
    while stack:
        for v in graph[stack.pop()]:
            if v not in seen:seen.add(v);stack.append(v)
    return seen
root=min(nodes);assert reach(adj,root)&reach(rev,root)==nodes
assert {e['source_edge'] for e in edges}=={int(i) for i in tight if int(base['U'][i]) in nodes and int(base['V'][i]) in nodes}
def acyclic(pairs,verts=None):
    verts=verts or ({u for u,v in pairs}|{v for u,v in pairs})
    degree=collections.Counter(v for u,v in pairs);out=collections.defaultdict(list)
    for u,v in pairs:out[u].append(v)
    queue=collections.deque(v for v in verts if degree[v]==0);seen=set()
    while queue:
        u=queue.popleft();seen.add(u)
        for v in out[u]:
            degree[v]-=1
            if degree[v]==0:queue.append(v)
    return seen==verts
rest=[(int(base['U'][i]),int(base['V'][i])) for i in tight if int(base['U'][i]) not in nodes and int(base['V'][i]) not in nodes]
assert acyclic(rest)
priorities=read('data/priorities.json')
actual=[i for i in range(len(windows)) if acyclic([(e['u'],e['v']) for e in edges if e['window']!=i],nodes)]
assert actual==priorities['single_pattern_cycle_covers'] and len(actual)==9
controls=[];statuses=collections.Counter()
for i in actual:
    row=windows[i];c=read(f'data/controls/w{i:02d}.json');screen=read(f'data/screen/w{i:02d}.json')
    statuses[screen['status']]+=1
    if c['status']=='SAT':
        W=[0]
        for d in row['directions']:W.append(W[-1]^(1<<d))
        alpha=forest(set(c['selected']),W);share=shares(set(c['selected']),W[1:-1])
        assert alpha==c['census']['alpha'] and share==c['census']['share']
        assert all(6<=a<=21 if b==6 else a==b for a,b in zip(alpha,row['counts']))
        controls.append(dict(window=i,share=sum(share)))
    else:assert c['status']=='UNSAT' and screen['status']=='SKIPPED'
assert len(controls)==7
rank=read('data/rank-certificate.json');mapping={v:i for i,v in enumerate(rank['original_nodes'])}
assert rank['edges']==[[mapping[e['u']],mapping[e['v']],e['window']] for e in edges]
assert all(w==1 or rank['ranks'][u]<rank['ranks'][v] for u,v,w in rank['edges'])
models=[]
for name in ['candidate','combined']:
    selected=read(f'data/selected-{name}.json')['selected']
    md=read(f'{name}/data/model.json');r=read(f'{name}/data/analysis-share.json')
    with np.load(HERE/name/'build/graph.npz') as z:a={k:z[k] for k in z.files}
    for k,h in md['arrays_sha256'].items():assert sha(a[k].tobytes())==h
    for k in ['U','V','direction','count','count_code']:assert np.array_equal(a[k],base[k])
    expected=base['share_lower'].copy()
    for di,ds in enumerate(meta['extensions']):
        ix=np.flatnonzero(base['direction']==di);shape=model.canon(ds[-6:])
        counts=np.array([decode(int(code))[-5:] for code in base['count_code'][ix]])
        for k in selected:
            row=windows[k]
            for word,cs in [(row['directions'],row['counts']),(row['directions'][::-1],row['counts'][::-1])]:
                if shape==model.canon(word):expected[ix]=np.maximum(expected[ix],np.where(np.all(counts==cs,axis=1),96,0))
    assert np.array_equal(expected,a['share_lower'])
    W=120*a['count'].astype(np.int64)+a['share_lower'];mean=Fraction(r['integer_weight_mean']);p,q=mean.numerator,mean.denominator
    raw=gzip.decompress((HERE/name/'data/potential-share.i64.gz').read_bytes());assert sha(raw)==r['potential_sha256']
    pi=np.frombuffer(raw,dtype='<i8');assert np.all(p+pi[a['V']]<=q*W+pi[a['U']])
    cycle=r['cycle']
    for j,row in enumerate(cycle):
        di=md['extensions'].index(row['directions']);code=int(model.code(np.array([row['counts']]))[0])
        hits=np.flatnonzero((a['direction']==di)&(a['count_code']==code));assert len(hits)==1;i=hits[0]
        assert row['state']==a['U'][i] and row['next_state']==a['V'][i]==cycle[(j+1)%len(cycle)]['state']
        assert row['weight']==W[i] and row['share_lower']==a['share_lower'][i]
    assert Fraction(sum(e['weight'] for e in cycle),len(cycle))==mean
    models.append(dict(name=name,selected=selected,mean=str(mean/120),cycle_length=len(cycle),zero_credit_cycle=all(e['share_lower']==0 for e in cycle)))
import re
lean=read('data/lean-check.json');assert len(lean['records'])==1
audits=[]
for r in lean['records']:
    assert r['exit_code']==0 and r['sha256']==sha((HERE/'lean'/r['source']).read_bytes())
    log=(HERE/'logs'/Path(r['source']).with_suffix('.log')).read_text()
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    entries += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(entries)==4
    for name,axioms in entries:
        assert {a.strip() for a in axioms.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
        audits.append(name)
out=dict(status='PASS',critical_states=37,critical_edges=48,windows=17,single_pattern_covers=actual,
    controls=controls,screen_status=dict(statuses),models=models,lean_audits=len(audits),
    scope='Finite graph coverage and potentials plus local positive geometry. The three new share-cap exclusions are numerical and have not passed Lean; no improved global bound.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
