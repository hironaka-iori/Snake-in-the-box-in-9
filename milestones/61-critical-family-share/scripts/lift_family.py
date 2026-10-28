"""Lift every critical-family transition through valid longer windows."""
from pathlib import Path
from fractions import Fraction
import collections,itertools,json
HERE=Path(__file__).resolve().parents[1]
def canon(ds):
    names={};return tuple(names.setdefault(x,len(names)) for x in ds)
def path(ds):
    w=[0]
    for d in ds:w.append(w[-1]^(1<<d))
    return w
def induced(w):
    return len(w)==len(set(w)) and all((w[i]^w[j]).bit_count()!=1 for i in range(len(w)) for j in range(i+2,len(w)))
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
pairs=list(itertools.combinations(range(9),2));geom={}
def geometry(ds):
    ds=tuple(ds)
    if ds in geom:return geom[ds]
    W=path(ds);D=set().union(*(NB[x] for x in W[1:-1]))-set(W);C=W[-6:-1];terms=[]
    for x in C:
        for q in sorted(NB[x]):
            empty=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in pairs)
            upper=len(NB[q]-D);assert upper>0
            credit=12*empty//upper
            if credit:terms.append(dict(centre=x,corner=q,empty=empty,degree_upper=upper,credit=credit))
    r=dict(directions=ds,vertices=W,centres=C,forced_absent=sorted(D),terms=terms,lower=sum(t['credit'] for t in terms))
    geom[ds]=r;return r
def rank_graph(edges):
    nodes={e['u'] for e in edges}|{e['v'] for e in edges};out=collections.defaultdict(list);deg=collections.Counter(e['v'] for e in edges)
    for e in edges:out[e['u']].append(e['v'])
    queue=collections.deque(sorted(v for v in nodes if deg[v]==0));rank={v:0 for v in nodes};seen=[]
    while queue:
        u=queue.popleft();seen.append(u)
        for v in out[u]:
            rank[v]=max(rank[v],rank[u]+1);deg[v]-=1
            if deg[v]==0:queue.append(v)
    return dict(acyclic=len(seen)==len(nodes),rank=[rank[i] for i in range(len(nodes))] if nodes==set(range(len(nodes))) else None,removed=len(seen))
previous=json.loads((HERE/'data/critical-edges.json').read_text())
previous=[dict(r,base_share=r['share_lower']) for r in previous]
for n in [10,11]:
    outgoing=collections.defaultdict(list)
    for j,e in enumerate(previous):outgoing[e['u']].append(j)
    unique={};rejected=[]
    for i,e in enumerate(previous):
        for j in outgoing[e['v']]:
            f=previous[j]
            assert e['counts'][1:]==f['counts'][:5]
            for d in range(min(9,max(e['directions'])+2)):
                ds=list(e['directions'])+[d]
                if canon(ds[1:])!=tuple(f['directions']):continue
                if not induced(path(ds)):
                    rejected.append(dict(previous_edges=[i,j],directions=ds));continue
                g=geometry(ds);lower=max(f['share_lower'],g['lower'])
                key=(tuple(ds),tuple(f['counts']))
                row=dict(directions=ds,counts=f['counts'],share_lower=lower,base_share=f['base_share'],
                         geometric_lower=g['lower'],weight=120*f['counts'][-1]+lower,previous_edges=[i,j])
                if key in unique:assert unique[key]['weight']==row['weight']
                else:unique[key]=row
    edges=list(unique.values());state_keys=set()
    for e in edges:
        state_keys.add((canon(e['directions'][:-1]),tuple(e['counts'][:-1])))
        state_keys.add((canon(e['directions'][1:]),tuple(e['counts'][1:])))
    keys=sorted(state_keys);sid={k:i for i,k in enumerate(keys)}
    for e in edges:
        e['u']=sid[(canon(e['directions'][:-1]),tuple(e['counts'][:-1]))]
        e['v']=sid[(canon(e['directions'][1:]),tuple(e['counts'][1:]))]
    result=dict(length=n,states=len(keys),edges=edges,state_keys=keys,rejected=rejected,**rank_graph(edges),
                scope='All valid longer-window transitions whose successive projections remain in the previously extracted critical family. Not the full snake model.')
    (HERE/f'data/lift-{n}.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Length',n,'states',len(keys),'edges',len(edges),'rejected',len(rejected),'acyclic',result['acyclic'],flush=True)
    previous=edges
(HERE/'data/geometry.json').write_text(json.dumps(dict(patterns=list(geom.values())),indent=2)+'\n')
