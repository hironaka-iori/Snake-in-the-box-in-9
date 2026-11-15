"""Check integer local weights that bound the number of edges for a prescribed seven-face."""
import argparse
import json
from itertools import combinations
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from dense_eight import components
from solve import save


def local_models(fixed,all_triples=False):
    fixed=set(fixed)
    adj=[{v^(1<<j) for j in range(7)} for v in range(128)]
    base=components(fixed,7)
    labels={v:i for i,(edges,part) in enumerate(base) for v in part}
    allowed={v for v in range(128) if v not in fixed or len(adj[v]&fixed)<2}
    features=[(v,) for v in sorted(allowed)]
    features+=sorted((v,w) for v in allowed for w in adj[v]&allowed if v<w)
    index={k:i for i,k in enumerate(features)}
    # The seven Fano-plane triples cover every axis, and rooted stars include
    # all neighbours of their centre. Their local constraints are hereditary.
    blocks={tuple(sorted(({v}|adj[v])&allowed)) for v in allowed}
    for j,k,l in combinations(range(7),3):
        if not all_triples and (j+1)^(k+1)^(l+1):continue
        dirs=(1<<j,1<<k,1<<l);mask=sum(dirs)
        for v in range(128):
            if v&mask:continue
            sites={v^sum(dirs[t] for t in range(3) if z&(1<<t)) for z in range(8)}
            blocks.add(tuple(sorted(sites&allowed)))
    models=[]
    for sites in sorted(blocks):
        if not sites:continue
        edges=[(i,j) for i,j in combinations(range(len(sites)),2) if sites[j] in adj[sites[i]]]
        ids=[index[(v,)] for v in sites]+[index[(sites[i],sites[j])] for i,j in edges]
        patterns=[]
        for selected in range(1<<len(sites)):
            parent=list(range(len(sites)+len(base)))
            def find(v):
                while parent[v]!=v:
                    v=parent[v]
                return v
            deg=[0]*len(sites);on=[];good=True
            for i,v in enumerate(sites):
                if selected&(1<<i):
                    on.append(i)
                    if v in fixed:parent[i]=len(sites)+labels[v];deg[i]=1
            for n,(i,j) in enumerate(edges,len(sites)):
                if not (selected&(1<<i) and selected&(1<<j)):continue
                on.append(n);deg[i]+=1;deg[j]+=1
                a,b=find(i),find(j)
                if a==b or max(deg[i],deg[j])>2:
                    good=False;break
                parent[a]=b
            if good:patterns.append(on)
        models.append((ids,patterns))
    return features,models,sum(e for e,part in base)


def calculate(fixed,size,certificate=None):
    features,models,base_edges=local_models(fixed)
    n=len(features);need=size-len(fixed)
    cost=[int(len(f)==2 or f[0] in fixed) for f in features]
    # For a two-vertex feature f[0] in fixed is immaterial to its unit cost.
    if certificate is None:
        row=[];col=[];data=[];rhs=[];moment=[];var=n
        for ids,patterns in models:
            norm=len(rhs);start=norm+1;rhs.extend([1]+[0]*len(ids));moment.append(start)
            for j,k in enumerate(ids):
                row.append(start+j);col.append(k);data.append(-1)
            for on in patterns:
                row.append(norm);col.append(var);data.append(1)
                for j in on:row.append(start+j);col.append(var);data.append(1)
                var+=1
        for j,f in enumerate(features):
            if len(f)==1:row.append(len(rhs));col.append(j);data.append(1)
        rhs.append(need)
        A=coo_matrix((data,(row,col)),shape=(len(rhs),var)).tocsr()
        objective=np.zeros(var);objective[:n]=-np.array(cost)
        lp=linprog(objective,A_eq=A,b_eq=rhs,bounds=(0,None),method="highs")
        assert lp.success,lp.message
        dual=lp.eqlin.marginals;D=600
        t=int(round(-dual[-1]*D))
        weights=[[int(round(x*D)) for x in dual[start:start+len(ids)]]
                 for start,(ids,_) in zip(moment,models)]
        # Repair numerical rounding to exact equalities on every feature.
        observed=[t if len(f)==1 else 0 for f in features];first={}
        for b,(ids,_) in enumerate(models):
            for j,i in enumerate(ids):observed[i]+=weights[b][j];first.setdefault(i,(b,j))
        for i,total in enumerate(observed):
            b,j=first[i];weights[b][j]+=D*cost[i]-total
        certificate=dict(scale=D,per_vertex=t,weights=weights)
    D,t,weights=(certificate[k] for k in ("scale","per_vertex","weights"))
    totals=[t if len(f)==1 else 0 for f in features]
    assert D>0 and len(weights)==len(models)
    upper=t*need
    for (ids,patterns),ws in zip(models,weights):
        assert len(ids)==len(ws) and all(type(w) is int for w in ws)
        for i,w in zip(ids,ws):totals[i]+=w
        upper+=max(sum(ws[j] for j in on) for on in patterns)
    assert totals==[D*c for c in cost]
    return dict(size=size,fixed=sorted(fixed),bound_numerator=base_edges*D+upper,
                max_edges=base_edges+upper//D,certificate=certificate)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("population",type=int);p.add_argument("start",type=int)
    p.add_argument("stop",type=int);p.add_argument("--replay",action="store_true");a=p.parse_args()
    rows=json.loads(Path("seven-deletion-classes.json").read_bytes())[str(a.population)]
    for i in range(a.start,min(len(rows),a.stop)):
        file=Path(f"forest-weight-{a.population}-{i}.json")
        cert=json.loads(file.read_bytes())["certificate"] if a.replay else None
        r=calculate(set(rows[i]["forest"]),117,cert)
        if a.replay:assert r==json.loads(file.read_bytes())
        else:save(file,r)
        print(a.population,i,r["max_edges"],flush=True)
