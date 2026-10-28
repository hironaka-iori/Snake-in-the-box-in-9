"""Separate verification of complete critical coverage, lifts and share weights."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def canon(ds):
    labels={};return tuple(labels.setdefault(x,len(labels)) for x in ds)
def path(ds):
    w=[0]
    for d in ds:w.append(w[-1]^(1<<d))
    return w
def induced(w):
    return len(set(w))==len(w) and all((w[i]^w[j]).bit_count()!=1 for i in range(len(w)) for j in range(i+2,len(w)))
def reach(adj,root):
    seen={root};todo=[root]
    while todo:
        for v in adj.get(todo.pop(),[]):
            if v not in seen:seen.add(v);todo.append(v)
    return seen
source=ROOT/'milestones/59-extended-share-window/extended'
md=read(source/'data/model.json');analysis=read(source/'data/analysis-share.json')
with np.load(source/'build/graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in md['arrays_sha256'].items():assert sha(a[k].tobytes())==h
raw=gzip.decompress((source/'data/potential-share.i64.gz').read_bytes());assert sha(raw)==analysis['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(analysis['integer_weight_mean']);p,q=mu.numerator,mu.denominator
weight=120*a['count'].astype(np.int64)+a['share_lower'];slack=q*weight+pi[a['U']]-pi[a['V']]-p
assert np.all(slack>=0)
tight=np.flatnonzero(slack==0);adj=collections.defaultdict(list);rev=collections.defaultdict(list)
for u,v in zip(a['U'][tight].tolist(),a['V'][tight].tolist()):adj[u].append(v);rev[v].append(u)
base=read(HERE/'data/critical-edges.json');nodes={r['u'] for r in base}|{r['v'] for r in base}
assert len(base)==74 and len(nodes)==49
root=min(nodes);assert reach(adj,root)&reach(rev,root)==nodes
expected={int(i) for i in tight if int(a['U'][i]) in nodes and int(a['V'][i]) in nodes}
assert expected=={r['source_edge'] for r in base}
rest_nodes=(set(adj)|set(rev))-nodes;degree={v:0 for v in rest_nodes}
for u in rest_nodes:
    for v in adj[u]:
        if v in rest_nodes:degree[v]+=1
queue=collections.deque(v for v in rest_nodes if degree[v]==0);removed=0
while queue:
    u=queue.popleft();removed+=1
    for v in adj[u]:
        if v in rest_nodes:
            degree[v]-=1
            if degree[v]==0:queue.append(v)
assert removed==len(rest_nodes)
for e in base:
    i=e['source_edge'];assert e['u']==a['U'][i] and e['v']==a['V'][i]
    assert e['weight']==weight[i] and e['share_lower']==a['share_lower'][i]
    assert e['directions']==md['extensions'][int(a['direction'][i])]
    assert e['counts']==[int(a['count_code'][i])//6**j%6+1 for j in range(5,-1,-1)]
source_inequalities=len(slack)
del a,slack,weight,pi,adj,rev,degree,rest_nodes

NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
faces=[];inc=[[] for _ in range(512)]
for i,j in itertools.combinations(range(9),2):
    mask=(1<<i)|(1<<j)
    for x in range(512):
        if x&mask:continue
        f=frozenset([x,x|(1<<i),x|(1<<j),x|mask]);faces.append(f)
        for v in f:inc[v].append(f)
assert len(set(faces))==4608
geometry=read(HERE/'data/geometry.json')['patterns'];lookup={tuple(r['directions']):r for r in geometry}
assert len(lookup)==len(geometry)==324
for r in geometry:
    w=path(r['directions']);s=set(w);assert w==r['vertices'] and induced(w)
    D={q for q in range(512) if any(len(NB[x]&(s|{q}))>2 for x in s)}
    assert sorted(D)==r['forced_absent'] and r['centres']==w[-6:-1]
    terms=[]
    for c in r['centres']:
        for z in sorted(NB[c]):
            empty=sum(f<=D for f in inc[z]);upper=len(NB[z]-D)
            assert upper>=1
            credit=12*empty//upper
            if credit:terms.append(dict(centre=c,corner=z,empty=empty,degree_upper=upper,credit=credit))
    assert terms==r['terms'] and sum(t['credit'] for t in terms)==r['lower']
previous=[dict(e,base_share=e['share_lower']) for e in base];lift_results=[]
for n in [10,11]:
    data=read(HERE/f'data/lift-{n}.json');expected={};rejected=set();out=collections.defaultdict(list)
    for j,e in enumerate(previous):out[e['u']].append(j)
    for i,e in enumerate(previous):
        for j in out[e['v']]:
            f=previous[j];assert e['counts'][1:]==f['counts'][:5]
            for ds in {canon(e['directions']+[k]) for k in range(9)}:
                if canon(ds[1:])!=tuple(f['directions']):continue
                if not induced(path(ds)):rejected.add((i,j,ds));continue
                g=lookup[ds]['lower'];share=max(g,f['share_lower'])
                key=(ds,tuple(f['counts']));value=(share,f['base_share'],g,120*f['counts'][-1]+share)
                if key in expected:assert expected[key]==value
                expected[key]=value
    assert rejected=={(r['previous_edges'][0],r['previous_edges'][1],tuple(r['directions'])) for r in data['rejected']}
    assert len(expected)==len(data['edges'])
    keys=set()
    for ds,cs in expected:keys.update([(canon(ds[:-1]),cs[:-1]),(canon(ds[1:]),cs[1:])])
    ordered=sorted(keys);sid={k:i for i,k in enumerate(ordered)}
    assert data['state_keys']==[[list(w),list(c)] for w,c in ordered]
    for e in data['edges']:
        ds,cs=tuple(e['directions']),tuple(e['counts'])
        assert expected[(ds,cs)]==(e['share_lower'],e['base_share'],e['geometric_lower'],e['weight'])
        assert e['u']==sid[(canon(ds[:-1]),cs[:-1])] and e['v']==sid[(canon(ds[1:]),cs[1:])]
    for _,_,ds in rejected:
        w=path(ds);assert len(set(w))==12
        assert all(len(NB[x]&set(w))==2 for x in w)
        assert [(i,j) for i in range(12) for j in range(i+2,12) if (w[i]^w[j]).bit_count()==1]==[(0,11)]
    lift_results.append(dict(length=n,states=len(keys),edges=len(expected),rejected_transitions=len(rejected),rejected_shapes=len({ds for _,_,ds in rejected})))
    previous=data['edges']
potential_results=[]
for result in read(HERE/'data/analyses.json'):
    n,mode=result['length'],result['mode'];data=read(HERE/f'data/lift-{n}.json');es=data['edges'];pi=result['potential']
    mu=Fraction(result['integer_mean']);p,q=mu.numerator,mu.denominator
    ws=[120*e['counts'][-1]+e['base_share'] if mode=='base' else e['weight'] for e in es]
    assert len(pi)==data['states'] and max(pi)-min(pi)==result['range']
    assert all(p+pi[e['v']]<=q*w+pi[e['u']] for e,w in zip(es,ws))
    cycle=result['cycle']
    assert cycle and all(es[e]['v']==es[cycle[(i+1)%len(cycle)]]['u'] for i,e in enumerate(cycle))
    assert Fraction(sum(ws[e] for e in cycle),len(cycle))==mu
    assert Fraction(result['normalized_mean'])==mu/120
    potential_results.append(dict(length=n,mode=mode,mean=str(mu),normalized_mean=str(mu/120),cycle_length=len(cycle),edge_checks=len(es)))
out=dict(status='PASS',source_edge_checks=source_inequalities,critical_states=49,critical_edges=74,
         components=1,geometry_shapes=324,positive_geometry=sum(r['lower']>0 for r in geometry),
         lifts=lift_results,potentials=potential_results,
         scope='The complete tight cyclic family of the source model, all longer-window transitions within that family, face-incidence credits, and four exact restricted graph means. This does not cover walks leaving the original critical family and establishes no global snake upper bound.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
