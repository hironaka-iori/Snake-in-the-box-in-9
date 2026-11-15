"""Integer edge bounds allowing arbitrary deletions from a half-full seven-cube template."""
import argparse
import json
from collections import deque
from itertools import combinations
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from seven_deletions import full_classes, IDENTITY, invert
from solve import save


def orbits(items,gens,action):
    remaining=set(items);groups=[]
    while remaining:
        first=min(remaining);remaining.remove(first);todo=[first];part=[first]
        while todo:
            x=todo.pop()
            for g in gens:
                y=action(x,g)
                if y in remaining:
                    remaining.remove(y);todo.append(y);part.append(y)
        groups.append(part)
    return groups


def blocks_and_features(fixed,gens,dimension):
    allowed=set(fixed)|set(range(128,256))
    features=[(v,) for v in sorted(allowed)]+sorted((v,v^(1<<j)) for v in allowed for j in range(8)
                                                      if (v^(1<<j)) in allowed and v<(v^(1<<j)))
    def act(feature,g):
        return tuple(sorted((v&128)|g[v&127] for v in feature))
    groups=orbits(features,gens,act)
    address_blocks={tuple(sorted([v,*[v^(1<<j) for j in range(7)]])) for v in range(128)}
    for axes in combinations(range(7),dimension):
        offsets=[sum(1<<ax for j,ax in enumerate(axes) if t&(1<<j)) for t in range(1<<dimension)]
        mask=offsets[-1]
        for v in range(128):
            if not v&mask:address_blocks.add(tuple(v|w for w in offsets))
    reps=[part[0] for part in orbits(address_blocks,gens,act)]
    return groups,reps


def patterns(fixed,U,missing,lookup):
    low=sorted(set(U)&fixed);sites=low+[v|128 for v in U];s=len(sites)
    edges=[(i,j) for i,j in combinations(range(s),2) if (sites[i]^sites[j]).bit_count()==1]
    labels=[lookup[(v,)] for v in sites]+[lookup[tuple(sorted((sites[i],sites[j])))] for i,j in edges]
    # Columns encode a literal induced graph on at most sixteen sites. Test
    # all subsets in parallel and remove cyclic graphs among those of degree <=2.
    N=1<<s;ids=np.arange(N,dtype=np.int32)
    on=((ids[:,None]>>np.arange(s))&1).astype(np.uint8)
    ok=np.sum(on[:,:len(low)],axis=1)>=len(low)-missing
    on=on[ok];ids=ids[ok];degree=np.zeros_like(on)
    selected_edges=np.empty((len(on),len(edges)),dtype=np.uint8)
    for k,(i,j) in enumerate(edges):
        active=on[:,i]&on[:,j];degree[:,i]+=active;degree[:,j]+=active;selected_edges[:,k]=active
    okay=np.max(degree,axis=1)<=2
    on=on[okay];ids=ids[okay];selected_edges=selected_edges[okay];degree=degree[okay]
    # Repeated removal of leaves empties a linear forest. A cycle leaves its
    # vertices alive after s rounds, even when a different component is a path.
    core=on.astype(bool)
    for _ in range(s):
        if not len(core):break
        degrees=np.zeros(core.shape,dtype=np.uint8)
        for i,j in edges:
            both=core[:,i]&core[:,j];degrees[:,i]+=both;degrees[:,j]+=both
        updated=core&(degrees>=2)
        if np.array_equal(core,updated):break
        core=updated
    keep=~core.any(axis=1)
    return labels,np.column_stack([on[keep],selected_edges[keep]])


def marked_template(index,base_size=64):
    rows=[list(map(int,line.split())) for line in Path("marked-seven-64.txt").read_text().splitlines()]
    data=json.loads(Path("seven-deletion-classes.json").read_bytes())[str(base_size)][index]
    h,g,_=full_classes(a|(b<<64) for a,b,c,w in rows)[data["full_class"]]
    if data["deleted"]:
        deleted=tuple(sorted(data["deleted"]));trans={deleted:IDENTITY};todo=deque([deleted])
        def act(d,perm):return tuple(sorted(perm[v] for v in d))
        while todo:
            d=todo.popleft()
            for gen in g:
                u=act(d,gen)
                if u not in trans:trans[u]=trans[d].translate(gen);todo.append(u)
        inv={d:invert(perm) for d,perm in trans.items()}
        g=sorted({perm.translate(gen).translate(inv[act(d,gen)])
                  for d,perm in trans.items() for gen in g}-{IDENTITY})
        h=h-set(deleted)
    assert h==set(data["forest"])
    assert all({p[v] for v in h}==h for p in g)
    return h,g


def solve(index,n,dim,replay=None,base_size=64,edge_floor=0,size=117):
    h,g=marked_template(index,base_size);features,blocks=blocks_and_features(h,g,dim)
    lookup={f:k for k,group in enumerate(features) for f in group}
    lowids=[k for k,group in enumerate(features) if len(group[0])==1 and group[0][0]<128]
    hiids=[k for k,group in enumerate(features) if len(group[0])==1 and group[0][0]>=128]
    local=[patterns(h,b,len(h)-n,lookup) for b in blocks]
    nfeat=len(features);need=size-n
    low_edges=[k for k,group in enumerate(features)
               if len(group[0])==2 and max(group[0])<128]
    cost=[len(group) if len(group[0])==2 else 0 for group in features]
    if replay is None:
        R=[];C=[];V=[];rhs=[];offset=nfeat;moments=[]
        for labels,ps in local:
            norm=len(rhs);start=norm+1;count=len(ps)
            rhs.extend([1]+[0]*len(labels));moments.append((start,len(labels)))
            R.append(np.full(count,norm));C.append(np.arange(offset,offset+count));V.append(np.ones(count))
            R.append(start+np.arange(len(labels)));C.append(np.array(labels));V.append(-np.ones(len(labels)))
            pid,feat=np.nonzero(ps)
            R.append(start+feat);C.append(offset+pid);V.append(np.ones(len(pid)));offset+=count
        for domain,k in ((lowids,n),(hiids,need)):
            R.append(np.full(len(domain),len(rhs)));C.append(np.array(domain));V.append(np.array([len(features[i]) for i in domain]));rhs.append(k)
        A=coo_matrix((np.concatenate(V),(np.concatenate(R),np.concatenate(C))),shape=(len(rhs),offset)).tocsr()
        obj=np.zeros(offset);obj[:nfeat]=-np.array(cost)
        extra={}
        floor_price=0
        if edge_floor:
            terms=np.array([-len(features[i]) for i in low_edges])
            lower_row=coo_matrix((terms,(np.zeros(len(low_edges),dtype=int),low_edges)),shape=(1,offset)).tocsr()
            extra=dict(A_ub=lower_row,b_ub=[-edge_floor])
        lp=linprog(obj,A_eq=A,b_eq=rhs,method="highs",**extra)
        if edge_floor and lp.status==2:
            # Replace an infeasible edge-floor row by a finite reward and use
            # its exact integer contribution in the final inequality.
            for i in low_edges:obj[i]-=1000*len(features[i])
            lp=linprog(obj,A_eq=A,b_eq=rhs,method="highs")
            floor_price=-1000
        elif edge_floor and lp.success:
            floor_price=lp.ineqlin.marginals[0]
        assert lp.success,lp.message
        D=1000000;dual=lp.eqlin.marginals;weights=[]
        for start,num in moments:weights.append([int(round(x*D)) for x in dual[start:start+num]])
        replay=dict(scale=D,lower=int(round(-D*dual[-2])),upper=int(round(-D*dual[-1])),weights=weights)
        if edge_floor:replay["lower_edges"]=min(0,int(round(D*floor_price)))
    D=replay["scale"];lo=replay["lower"];hi=replay["upper"];weights=replay["weights"]
    numer=n*lo+need*hi;balance=[0]*len(features)
    for domain,charge in ((lowids,lo),(hiids,hi)):
        for i in domain:balance[i]+=charge*len(features[i])
    if edge_floor:
        q=replay["lower_edges"]
        assert q<=0
        numer+=q*edge_floor
        for i in low_edges:balance[i]+=q*len(features[i])
    assert len(local)==len(weights) and D>0
    for (labels,valid),ws in zip(local,weights):
        assert len(labels)==len(ws)
        for i,w in zip(labels,ws):balance[i]+=w
        # Avoid fixed-width overflow if a future certificate uses larger weights.
        assert sum(abs(w) for w in ws)<2**62
        numer+=int((valid@np.array(ws,dtype=np.int64)).max())
    numer+=sum(max(0,D*v-b) for v,b in zip(cost,balance))
    record=dict(template=index,lower_size=n,upper_size=need,dimension=dim,edge_upper=numer//D,
                numerator=numer,certificate=replay,feature_orbits=len(features),block_orbits=len(blocks))
    if edge_floor:record["minimum_lower_edges"]=edge_floor
    return record


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("index",type=int);p.add_argument("population",type=int)
    p.add_argument("--dimension",type=int,default=3,choices=(2,3));p.add_argument("--replay",action="store_true")
    p.add_argument("--base",type=int,default=64,choices=(62,63,64))
    p.add_argument("--edges",type=int,default=0);p.add_argument("--size",type=int,default=117)
    a=p.parse_args();prefix="variable-facet" if a.base==64 else f"variable-mark-{a.base}"
    extra=(f"-edges{a.edges}" if a.edges else "")+(f"-size{a.size}" if a.size!=117 else "")
    file=Path(f"{prefix}-{a.index}-{a.population}-{a.dimension}{extra}.json")
    cert=json.loads(file.read_bytes())["certificate"] if a.replay else None
    r=solve(a.index,a.population,a.dimension,cert,a.base,a.edges,a.size)
    if a.base!=64:r["base_size"]=a.base
    if cert:assert r==json.loads(file.read_bytes())
    else:save(file,r)
    print(a.index,a.population,r["edge_upper"],r["feature_orbits"],r["block_orbits"],flush=True)
