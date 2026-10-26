"""Independent geometry, graph-coverage, and integer-potential checks."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/52-share-on-235/scripts'))
from geometry_helpers import forest,shares
np=model.np
def read(p):return json.loads((HERE/p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def key(ds,cs):return min((model.canon(ds),tuple(cs)),(model.canon(ds[::-1]),tuple(cs[::-1])))
def decode(code):return tuple(code//6**j%6+1 for j in range(5,-1,-1))

source=ROOT/'milestones/54-share-coverage/proposed-bidirectional'
meta=json.loads((source/'data/model.json').read_text());analysis=json.loads((source/'data/analysis-share.json').read_text())
with np.load(source/'build/graph.npz') as z:base={k:z[k] for k in z.files}
for k,digest in meta['arrays_sha256'].items():assert sha(base[k].tobytes())==digest
encoded=gzip.decompress((source/'data/potential-share.i64.gz').read_bytes());assert sha(encoded)==analysis['potential_sha256']
pi=np.frombuffer(encoded,dtype='<i8');mean=Fraction(analysis['integer_weight_mean']);p,q=mean.numerator,mean.denominator
slack=q*(120*base['count'].astype(np.int64)+base['share_lower'])+pi[base['U']]-pi[base['V']]-p
assert np.all(slack>=0)
edges=read('data/critical-edges.json');ids=[e['source_edge'] for e in edges];nodes={e['u'] for e in edges}|{e['v'] for e in edges}
assert len(edges)==83 and len(nodes)==57
windows=read('data/windows.json')
for e in edges:
    i=e['source_edge'];assert base['U'][i]==e['u'] and base['V'][i]==e['v'] and slack[i]==0
    ds=meta['extensions'][int(base['direction'][i])][-6:];cs=decode(int(base['count_code'][i]))[-5:]
    row=windows[e['window']];assert key(ds,cs)==(tuple(row['directions']),tuple(row['counts']))

# Independently prove the recorded component is the only cyclic component of the tight graph.
tight=np.flatnonzero(slack==0);adj=collections.defaultdict(list);rev=collections.defaultdict(list)
for u,v in zip(base['U'][tight].tolist(),base['V'][tight].tolist()):adj[u].append(v);rev[v].append(u)
def reachable(graph,root):
    seen={root};stack=[root]
    while stack:
        for v in graph[stack.pop()]:
            if v not in seen:seen.add(v);stack.append(v)
    return seen
root=min(nodes);assert reachable(adj,root)&reachable(rev,root)==nodes
assert set(ids)=={int(i) for i in tight if int(base['U'][i]) in nodes and int(base['V'][i]) in nodes}
rest=[(int(base['U'][i]),int(base['V'][i])) for i in tight if int(base['U'][i]) not in nodes and int(base['V'][i]) not in nodes]
rest_nodes={u for u,v in rest}|{v for u,v in rest};degree=collections.Counter(v for u,v in rest);other=collections.defaultdict(list)
for u,v in rest:other[u].append(v)
queue=collections.deque(v for v in rest_nodes if degree[v]==0);seen=set()
while queue:
    u=queue.popleft();seen.add(u)
    for v in other[u]:
        degree[v]-=1
        if degree[v]==0:queue.append(v)
assert seen==rest_nodes

rank=read('data/rank-certificate.json');mapping={v:i for i,v in enumerate(rank['original_nodes'])}
assert rank['edges']==[[mapping[e['u']],mapping[e['v']],e['window']] for e in edges]
assert all(w==6 or rank['ranks'][u]<rank['ranks'][v] for u,v,w in rank['edges'])
cycle=read('data/cycle-cover.json')['share_only']['cycle_constraints'][0]['cycle']
assert cycle and all(edges[e]['v']==edges[cycle[(j+1)%len(cycle)]]['u'] for j,e in enumerate(cycle))

controls=[];statuses=collections.Counter()
for i,row in enumerate(windows):
    control=read(f'data/controls/w{i:02d}.json');screen=read(f'data/screen/w{i:02d}.json');statuses[screen['status']]+=1
    if control['status']=='SAT':
        W=[0]
        for d in row['directions']:W.append(W[-1]^(1<<d))
        alpha=forest(set(control['selected']),W);share=shares(set(control['selected']),W[1:-1])
        assert alpha==control['census']['alpha'] and share==control['census']['share']
        assert all(6<=a<=21 if c==6 else a==c for a,c in zip(alpha,row['counts']))
        controls.append(dict(row=i,share=sum(share),sha256=sha((HERE/f'data/controls/w{i:02d}.json').read_bytes())))
    else:assert control['status']=='UNSAT' and screen['status']=='SKIPPED'
assert len(controls)==25

models=[]
for name in ['covered','count-control']:
    md=read(f'{name}/data/model.json');r=read(f'{name}/data/analysis-share.json')
    with np.load(HERE/name/'build/graph.npz') as z:a={k:z[k] for k in z.files}
    for k,digest in md['arrays_sha256'].items():assert sha(a[k].tobytes())==digest
    keep=np.ones(len(base['U']),dtype=bool)
    if name=='count-control':
        row=windows[9]
        for di,ds in enumerate(meta['extensions']):
            ids0=np.flatnonzero(base['direction']==di)
            shape=model.canon(ds[-6:]);counts=np.array([decode(int(c))[-5:] for c in base['count_code'][ids0]])
            for word,cs in [(row['directions'],row['counts']),(row['directions'][::-1],row['counts'][::-1])]:
                if shape==model.canon(word):keep[ids0]&=~np.all(counts==cs,axis=1)
    for field in ['U','V','count','direction','count_code']:assert np.array_equal(a[field],base[field][keep])
    expected=base['share_lower'][keep].copy()
    if name=='covered':
        row=windows[6]
        for di,ds in enumerate(meta['extensions']):
            ix=np.flatnonzero(a['direction']==di);shape=model.canon(ds[-6:])
            counts=np.array([decode(int(c))[-5:] for c in a['count_code'][ix]])
            for word,cs in [(row['directions'],row['counts']),(row['directions'][::-1],row['counts'][::-1])]:
                if shape==model.canon(word):expected[ix]=np.maximum(expected[ix],np.where(np.all(counts==cs,axis=1),96,0))
    assert np.array_equal(expected,a['share_lower'])
    W=120*a['count'].astype(np.int64)+a['share_lower'];mean=Fraction(r['integer_weight_mean']);p,q=mean.numerator,mean.denominator
    encoded=gzip.decompress((HERE/name/'data/potential-share.i64.gz').read_bytes());assert sha(encoded)==r['potential_sha256']
    pi=np.frombuffer(encoded,dtype='<i8');assert np.all(p+pi[a['V']]<=q*W+pi[a['U']])
    cycle=r['cycle']
    for j,row in enumerate(cycle):
        di=md['extensions'].index(row['directions']);code=int(model.code(np.array([row['counts']]))[0])
        hits=np.flatnonzero((a['direction']==di)&(a['count_code']==code));assert len(hits)==1;e=hits[0]
        assert row['state']==a['U'][e] and row['next_state']==a['V'][e]==cycle[(j+1)%len(cycle)]['state']
        assert row['weight']==W[e] and row['share_lower']==a['share_lower'][e]
    assert Fraction(sum(c['weight'] for c in cycle),len(cycle))==mean
    models.append(dict(name=name,mean=str(mean/120),edges=len(W),cycle_length=len(cycle),potential_range=int(pi.max()-pi.min())))
out=dict(status='PASS',critical_edges=83,critical_states=57,critical_windows=26,selected_cover=[6],
    positive_controls=controls,screen_status=dict(statuses),models=models,
    scope='Independent finite-model coverage, controls and potentials. Numerical premises and global snake assembly remain separate.')
(HERE/'data/finite-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='positive_controls'})
