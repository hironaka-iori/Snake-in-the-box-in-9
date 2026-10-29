"""Independent complete critical-family, context and empty-face reconstruction."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic()
SOURCE=ROOT/'milestones/66-full-model-and-revision';meta=read(SOURCE/'data/pressured-model.json');analysis=read(SOURCE/'data/pressured-analysis.json')
with np.load(SOURCE/'build/pressured-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
raw=gzip.decompress((SOURCE/'data/pressured-potential.i64.gz').read_bytes());assert sha(raw)==analysis['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(analysis['integer_mean']);p,d=mu.numerator,mu.denominator
slack=d*a['weight'].astype(np.int64)+pi[a['U']]-pi[a['V']]-p;assert np.all(slack>=0)
ids=np.flatnonzero(slack==0);adj=collections.defaultdict(list);rev=collections.defaultdict(list)
for u,v in zip(a['U'][ids].tolist(),a['V'][ids].tolist()):adj[u].append(v);rev[v].append(u)
def reach(graph,root):
    seen={root};todo=[root]
    while todo:
        for v in graph.get(todo.pop(),[]):
            if v not in seen:seen.add(v);todo.append(v)
    return seen
base=read(SOURCE/'data/critical-edges.json');nodes={e['u'] for e in base}|{e['v'] for e in base}
assert len(nodes)==70 and len(base)==99
root=min(nodes);assert reach(adj,root)&reach(rev,root)==nodes
expected={int(i) for i in ids if int(a['U'][i]) in nodes and int(a['V'][i]) in nodes}
assert expected=={e['edge'] for e in base}
rest=(set(adj)|set(rev))-nodes;deg={v:0 for v in rest}
for u in rest:
    for v in adj[u]:
        if v in rest:deg[v]+=1
queue=collections.deque(v for v in rest if deg[v]==0);removed=0
while queue:
    u=queue.popleft();removed+=1
    for v in adj[u]:
        if v in rest:
            deg[v]-=1
            if deg[v]==0:queue.append(v)
assert removed==len(rest)
original=ROOT/'milestones/59-extended-share-window/extended';om=read(original/'data/model.json')
with np.load(original/'build/graph.npz') as z:o={k:z[k] for k in ['direction','count_code']}
for e in base:
    i=e['edge'];j=a['source_edge'][i]
    assert (e['u'],e['v'],e['weight'],e['history'])==(a['U'][i],a['V'][i],a['weight'][i],a['history'][i])
    assert e['directions']==om['extensions'][int(o['direction'][j])]
    assert e['counts']==[int(o['count_code'][j])//6**k%6+1 for k in range(5,-1,-1)]
del a,pi,slack,adj,rev,rest,deg,o
def canon(ds):
    labels=list(dict.fromkeys(ds));return tuple(labels.index(x) for x in ds)
def vertices(ds):
    W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    return W
def induced(W):return len(set(W))==len(W) and all((W[i]^W[j]).bit_count()!=1 for j in range(len(W)) for i in range(j-1))
outgoing=collections.defaultdict(list)
for i,e in enumerate(base):outgoing[e['u']].append(i)
expected=set();invalid=set();dead=[]
for i,e in enumerate(base):
    for j in outgoing[e['v']]:
        f=base[j];assert e['counts'][1:]==f['counts'][:-1]
        for k in outgoing[f['v']]:
            g=base[k];assert f['counts'][1:]==g['counts'][:-1];accepted=0
            for c in range(min(9,max(e['directions'])+2)):
                ten=tuple(e['directions'])+(c,)
                if canon(ten[1:])!=tuple(f['directions']):continue
                for z in range(min(9,max(ten)+2)):
                    word=ten+(z,)
                    if canon(word[2:])!=tuple(g['directions']):continue
                    W=vertices(word)
                    if induced(W):expected.add((i,j,k,word));accepted+=1
                    else:invalid.add(word)
            if not accepted:dead.append([i,j,k])
family=read(HERE/'data/family.json');edges=family['edges'];keys=family['state_keys']
assert expected=={tuple(e['source_edges'])+(tuple(e['directions']),) for e in edges}
assert len(expected)==len(edges) and dead==family['rejected_triples']
for e in edges:
    i,j,k=e['source_edges'];w=e['directions']
    assert keys[e['u']]==[i,j,list(canon(w[:10]))] and keys[e['v']]==[j,k,list(canon(w[1:]))]
    assert e['counts']==base[k]['counts'] and e['original_weight']==base[k]['weight']
NB=[{y for y in range(512) if (x^y).bit_count()==1} for x in range(512)];faces=[];incident=[[] for _ in range(512)]
for c,z in itertools.combinations(range(9),2):
    for x in range(512):
        if x&(1<<c) or x&(1<<z):continue
        F={x,x^(1<<c),x^(1<<z),x^(1<<c)^(1<<z)};faces.append(F)
        for q in F:incident[q].append(F)
assert len(faces)==4608
geos={}
for r in read(HERE/'data/geometry.json'):
    W=vertices(r['directions']);assert W==r['vertices'] and induced(W) and r['centres']==W[6:11]
    D=set().union(*(NB[x] for x in W[1:-1]))-set(W);assert D==set(r['absent'])
    value=0
    for x in W[6:11]:
        for q in NB[x]:
            upper=len(NB[q]-D);assert upper>0
            value+=12*sum(F<=D for F in incident[q])//upper
    assert value==r['lower'];geos[tuple(r['directions'])]=value
for e in edges:
    value=geos[tuple(e['directions'])];assert value==e['geometric_lower']
    assert e['weight']==max(e['original_weight'],120*e['counts'][-1]+value)
for word in invalid:
    W=vertices(word);assert len(W)==12 and len(set(W))==12
    assert all(len(NB[v]&set(W))==2 for v in W)
(HERE/'data/rejected-words.json').write_text(json.dumps([list(w) for w in sorted(invalid)],indent=2)+'\n')
for result in read(HERE/'data/analyses.json'):
    pi=result['potential'];mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator;mode=result['mode']
    assert all(p+pi[e['v']]<=d*e[mode]+pi[e['u']] for e in edges)
    cy=[edges[i] for i in result['cycle']];assert cy
    assert all(e['v']==cy[(j+1)%len(cy)]['u'] for j,e in enumerate(cy))
    assert d*sum(e[mode] for e in cy)==p*len(cy)
out=dict(status='PASS',source_states=70,source_edges=99,all_source_inequalities=meta['edges'],
    states=family['states'],edges=len(edges),shapes=len(geos),improved_edges=family['improved_edges'],
    rejected_direction_shapes=len(invalid),rejected_triples=len(dead),seconds=time.monotonic()-start,
    scope='Independent complete critical-family extraction, all lifted contexts, empty-square counts and both finite potentials. Lean audits and global coverage are separate.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
