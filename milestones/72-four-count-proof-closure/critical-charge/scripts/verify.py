"""Independently verify cyclic tight edges by connectivity and acyclic contraction."""
from pathlib import Path
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
meta=read(HERE/'data/source-proved-model.json');family=read(HERE/'data/critical-family.json')
records=read(HERE/'data/critical-edges.json');windows=read(HERE/'data/windows.json')
with np.load(HERE/'build/source-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
raw=gzip.decompress((HERE/'data/source-potential.i64.gz').read_bytes());assert sha(raw)==family['source_potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');slack=a['weight'].astype(np.int64)+pi[a['U']]-pi[a['V']]-480
assert np.all(slack>=0);tight=np.flatnonzero(slack==0)
N=len(pi);labels=np.arange(N,dtype=np.int64);members={}
for c in family['components']:
    rows=[r for r in records if r['component']==c['id']]
    vs={r['u'] for r in rows}|{r['v'] for r in rows};assert len(vs)==c['states'] and len(rows)==c['edges']
    for reverse in [False,True]:
        adj=collections.defaultdict(list)
        for r in rows:adj[r['v'] if reverse else r['u']].append(r['u'] if reverse else r['v'])
        todo=[next(iter(vs))];seen=set()
        while todo:
            v=todo.pop()
            if v in seen:continue
            seen.add(v);todo.extend(adj[v])
        assert seen==vs
    new=N+len(members);members[c['id']]=vs;labels[list(vs)]=new
u=labels[a['U'][tight]];v=labels[a['V'][tight]]
assert set(tight[u==v].tolist())=={r['source_edge'] for r in records}
# Contract the stated cyclic components. Any omitted cycle would survive here.
keep=u!=v;u=u[keep];v=v[keep];size=N+len(members)
order=np.argsort(u,kind='stable');u=u[order];v=v[order]
starts=np.searchsorted(u,np.arange(size+1));indegree=np.bincount(v,minlength=size)
active=np.zeros(size,dtype=bool);active[u]=True;active[v]=True
queue=list(np.flatnonzero(active & (indegree==0)));processed=0
while queue:
    node=queue.pop();processed+=1
    for target in v[starts[node]:starts[node+1]]:
        indegree[target]-=1
        if indegree[target]==0:queue.append(int(target))
assert processed==int(active.sum())
def canon(ds):
    seen={};return tuple(seen.setdefault(d,len(seen)) for d in ds)
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
for r in records:
    i=r['source_edge'];assert int(a['U'][i])==r['u'] and int(a['V'][i])==r['v'] and int(a['weight'][i])==r['weight']
    ds=sm['extensions'][int(a['direction'][i])];counts=tuple(int(a['count_code'][i])//6**j%6+1 for j in range(5,-1,-1))
    assert ds==r['directions'] and list(counts)==r['counts']
    key=min((canon(ds[-6:]),counts[-5:]),(canon(ds[-6:][::-1]),counts[-5:][::-1]))
    w=windows[r['window']];assert key==(tuple(w['directions']),tuple(w['counts']))
    assert r['share_lower']==r['weight']-120*counts[-1]==0
out=dict(status='PASS',critical_edges=len(records),critical_states=sum(map(len,members.values())),components=len(members),windows=len(windows),contracted_graph_acyclic=True,all_recorded_components_strongly_connected=True,source_cases=meta['applied_cases'],source_arrays_sha256=meta['arrays_sha256'],source_potential_sha256=sha(raw),scope='Independent finite-graph check only. Does not establish the arbitrary-snake graph interpretation or any new upper bound.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
