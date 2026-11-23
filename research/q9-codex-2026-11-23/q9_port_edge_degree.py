"""Endpoint and square constraints for paths of ANY length containing specified ports."""
import gzip,json
from itertools import combinations
from q9_overlapping_port_bound import ROOT,NEIGH,controls,constraints as overlap

def build(edges):
    req={v for e in edges for v in e}
    adj=[set(w for w in ns if w in req) for ns in NEIGH]
    sat={v for v in req if len(adj[v])==2}
    free=sorted(v for v in range(512) if v not in req and len(adj[v])<=2 and not adj[v]&sat)
    ix={v:i for i,v in enumerate(free)}
    core,n,rows=overlap(edges)
    assert n==len(free)
    bonds={}
    for v in free:
        for w in NEIGH[v]:
            if w in ix and v<w:
                j=n+len(bonds);bonds[v,w]=j
                rows.extend([([j,ix[v]],[1,-1],0),([j,ix[w]],[1,-1],0),
                             ([ix[v],ix[w],j],[1,1,-1],1)])
    for v in free:
        ep=[bonds[min(v,w),max(v,w)] for w in NEIGH[v] if w in ix]
        rows.append((ep+[ix[v]],[1]*len(ep)+[len(adj[v])-2],0))
    # A nonempty path has exactly |V|-1 induced edges.
    ids=[*range(n),*bonds.values()]
    co=[1-len(adj[v]) for v in free]+[-1]*len(bonds)
    rows.append((ids,co,1-core+sum(len(adj[v]) for v in req)//2))
    # In each square, the selected edges form a forest; root it at each corner.
    for a,b in combinations(range(9),2):
        mask=(1<<a)|(1<<b)
        for v in range(512):
            if v&mask:continue
            q=[v,v^(1<<a),v^mask,v^(1<<b)]
            if any(x not in req and x not in ix for x in q):continue
            for root in q:
                terms={}; fixed=0
                def add(j,k):terms[j]=terms.get(j,0)+k
                for x,y in zip(q,q[1:]+q[:1]):
                    if x in req and y in req:fixed+=1
                    elif x in req:add(ix[y],1)
                    elif y in req:add(ix[x],1)
                    else:add(bonds[min(x,y),max(x,y)],1)
                for x in q:
                    if x==root:continue
                    if x in req:fixed-=1
                    else:add(ix[x],-1)
                rows.append((list(terms),list(terms.values()),-fixed))
    return core,n,n+len(bonds),rows

def replay(edges,weights,den,builder=build):
    c,n,N,rows=builder(edges)
    lhs=[0]*N;cost=c*den
    for i,w in weights:
        assert isinstance(w,int) and w>=0 and 0<=i<len(rows)
        ix,co,rhs=rows[i];cost+=w*rhs
        for j,t in zip(ix,co):lhs[j]+=w*t
    return (cost+sum(max(0,(den if j<n else 0)-t) for j,t in enumerate(lhs)))//den-1

def solve(edges,builder=build):
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    c,n,N,rows=builder(edges)
    ix=[];vals=[];ptr=[0]
    for ids,co,_ in rows:
        ix.extend(ids);vals.extend(co);ptr.append(len(ix))
    A=csr_matrix((vals,ix,ptr),shape=(len(rows),N))
    lp=linprog([-1]*n+[0]*(N-n),A_ub=A,b_ub=[r[2] for r in rows],bounds=(0,1),method="highs")
    if lp.status==2:
        from scipy.sparse import hstack
        import numpy as np
        # Every real path is feasible with zero slack. The extra variable makes
        # it possible to extract a separating dual also on impossible inputs.
        relaxed=hstack([A,-np.ones((A.shape[0],1))],format="csr")
        lp=linprog([-1]*n+[0]*(N-n)+[10000],A_ub=relaxed,b_ub=[r[2] for r in rows],
                   bounds=[(0,1)]*N+[(0,None)],method="highs")
    assert lp.success,lp.message
    den=100000
    weights=[(i,round(-x*den)) for i,x in enumerate(lp.ineqlin.marginals) if round(-x*den)>0]
    return replay(edges,weights,den,builder),den,weights

if __name__=="__main__":
    import sys
    with gzip.open(ROOT/"q9_port_edge_degree_131.jsonl.gz","wt") as f:
        for i,es in enumerate(controls()):
            b,d,w=solve(es)
            assert b>=191
            f.write(json.dumps(dict(row=i,edges=es,upper=b,den=d,weights=w))+"\n")
            print(i,b,flush=True)
