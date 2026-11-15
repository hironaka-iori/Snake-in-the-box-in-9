"""Exact two-copy separation of cycle parity at saved rational points."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import hashlib,heapq,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
summary=[]
for root in [0,78]:
    mp=H/'data'/f'square-{root}'/'model.json';m=json.loads(mp.read_bytes())
    pp=H/'data'/f'rational-{root}'/'primal-certificate.json';p=json.loads(pp.read_bytes())
    q=[Q(*x) for x in p['values']];D=lcm(*(x.denominator for x in q));z=[int(x*D) for x in q]
    V=m['vertices'];pos={v:i for i,v in enumerate(V)};names={n:i for i,n in enumerate(m['variables'])};G=[[] for _ in range(2*len(V))]
    for ei,(u,v) in enumerate(m['edges']):
        d=z[names[f'x{u}']]+z[names[f'x{v}']]-2*z[names[f'y{u}_{v}']];assert 0<=d<=D
        for bit in [0,1]:
            for flip in [0,1]:
                a=2*pos[u]+bit;b=2*pos[v]+(bit^flip);cost=D-d if flip else d
                G[a].append((b,cost,ei,flip));G[b].append((a,cost,ei,flip))
    violations={};potentials=[];minimum=None
    for vi,v in enumerate(V):
        start=2*vi;target=start+1;dist={start:0};previous={};heap=[(0,start)];done=set()
        while heap:
            d,u=heapq.heappop(heap)
            if u in done:continue
            done.add(u)
            for w,c,ei,flip in G[u]:
                if w in done:continue
                nd=d+c
                if w not in dist or nd<dist[w]:dist[w]=nd;previous[w]=(u,ei,flip);heapq.heappush(heap,(nd,w))
        assert len(dist)==2*len(V)
        assert all(dist[w]-dist[u]<=c for u,adj in enumerate(G) for w,c,ei,f in adj)
        minimum=dist[target] if minimum is None else min(minimum,dist[target])
        potentials.append({'source':v,'values':[dist[i] for i in range(len(G))]})
        if dist[target]>=D:continue
        path=[target];transitions=[]
        while path[-1]!=start:
            old,ei,flip=previous[path[-1]];transitions.append((ei,flip));path.append(old)
        path.reverse();transitions.reverse();seen={};a=b=None
        for k,state in enumerate(path):
            vertex=state//2
            if vertex in seen:a=seen[vertex];b=k;break
            seen[vertex]=k
        assert a is not None
        states=path[a:b];ce=transitions[a:b];C=[V[s//2] for s in states];F=[i for i,(_,flip) in enumerate(ce) if flip]
        assert len(C)>=4 and len(C)==len(set(C)) and len(F)%2==1
        edges=[m['edges'][ei] for ei,f in ce];cost=0
        for i,(u,w) in enumerate(edges):
            d=z[names[f'x{u}']]+z[names[f'x{w}']]-2*z[names[f'y{u}_{w}']]
            cost+=D-d if i in F else d
        assert cost<D
        key=tuple(sorted((ei,flip) for ei,flip in ce))
        violations[key]={'cycle':C,'edges':edges,'odd_edge_indices':F,'scaled_cost':cost,'scaled_violation':D-cost}
    out=H/'data'/f'cut-diagnostic-{root}.json';assert not out.exists()
    report={'root':root,'model_sha256':sha(mp),'primal_sha256':sha(pp),'source_sha256':sha(__file__),'scale':D,
        'minimum_scaled_odd_walk_cost':minimum,'complete_cycle_parity':minimum>=D,'violations':list(violations.values()),
        'potentials':potentials if minimum>=D else [],'scope':'Exact rational separation; each saved violation is a simple cycle with an odd edge subset.'}
    out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    s={'root':root,'violated_cycles':len(violations),'minimum_cost':[minimum,D],'lengths':sorted(set(len(v['cycle']) for v in violations.values())),'complete_cycle_parity':minimum>=D}
    summary.append(s);print(json.dumps(s),flush=True)
(H/'data/cut-diagnostic-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
