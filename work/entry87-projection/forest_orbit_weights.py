"""Compress local forest weights by exact incidence counts, then verify them on literal blocks."""
import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from forest_weight_bound import local_models
from solve import save


def identify(values):
    keys={};ids=[]
    for v in values:ids.append(keys.setdefault(v,len(keys)))
    return ids


def refine(features,models,fixed):
    colors=identify((len(f),int(f[0] in fixed and len(f)==1)) for f in features)
    intrinsic=[]
    for ids,patterns in models:
        degree=Counter(v for i in ids if len(features[i])==2 for v in features[i])
        freq=Counter(j for p in patterns for j in p)
        intrinsic.append([(tuple(sorted(degree[v] for v in features[i])),freq[j]) for j,i in enumerate(ids)])
    while True:
        signatures=[];local=[];roles=[]
        for (ids,patterns),labels in zip(models,intrinsic):
            cols=[(colors[i],label) for i,label in zip(ids,labels)]
            possibilities={tuple(sorted(cols[j] for j in on)) for on in patterns}
            sig=(tuple(sorted(cols)),tuple(sorted(possibilities)))
            signatures.append(sig);local.append(sorted(set(cols)));roles.append(cols)
        types=identify(signatures)
        incid=[[] for _ in features]
        for b,(ids,_),cs in zip(types,models,roles):
            for i,k in zip(ids,cs):incid[i].append((b,k))
        new=identify((c,tuple(sorted(v))) for c,v in zip(colors,incid))
        if len(set(new))==len(set(colors)):break
        colors=new
    classes=defaultdict(list)
    for i,t in enumerate(types):classes[t].append(i)
    return colors,classes,signatures,local,roles


def bound(fixed,size,cert=None):
    features,models,base=local_models(fixed,True)
    colors,classes,sigs,local,roles=refine(features,models,fixed)
    sizes=Counter(colors);n=len(sizes);need=size-len(fixed)
    vertex={c for c,f in zip(colors,features) if len(f)==1}
    costs={c:int(len(f)==2 or f[0] in fixed) for c,f in zip(colors,features)}
    if cert is None:
        row=[];col=[];coeff=[];rhs=[];moment=[];var=n
        for b,group in classes.items():
            first=group[0];mult=Counter(sigs[first][0]);cs=local[first]
            norm=len(rhs);start=norm+1;rhs.extend([1]+[0]*len(cs));moment.append((start,len(cs)))
            jrow={k:start+i for i,k in enumerate(cs)}
            for k in cs:row.append(jrow[k]);col.append(k[0]);coeff.append(-mult[k])
            for pattern in sigs[first][1]:
                row.append(norm);col.append(var);coeff.append(1)
                for k,m in Counter(pattern).items():row.append(jrow[k]);col.append(var);coeff.append(m)
                var+=1
        for k in vertex:row.append(len(rhs));col.append(k);coeff.append(sizes[k])
        rhs.append(need)
        A=coo_matrix((coeff,(row,col)),shape=(len(rhs),var)).tocsr()
        obj=np.zeros(var);obj[:n]=[-sizes[k]*costs[k] for k in range(n)]
        lp=linprog(obj,A_eq=A,b_eq=rhs,bounds=(0,None),method="highs")
        penalty=None
        if lp.status==2:
            # A dense opposite side may already be impossible by population.
            # Reward each chosen vertex strongly, remove the population
            # equality, and subtract its known reward in the integer check.
            penalty=10000
            for k in vertex:obj[k]-=penalty*sizes[k]
            lp=linprog(obj,A_eq=A[:-1],b_eq=rhs[:-1],bounds=(0,None),method="highs")
        assert lp.success,lp.message
        dual=lp.eqlin.marginals;D=1000000
        t=-penalty*D if penalty is not None else int(round(-dual[-1]*D))
        weights=[]
        for (start,length),group in zip(moment,classes.values()):
            weights.append([int(round(v*D/len(group))) for v in dual[start:start+length]])
        cert=dict(scale=D,per_vertex=t,weights=weights)
    D,t,W=cert["scale"],cert["per_vertex"],cert["weights"]
    assert D>0 and len(W)==len(classes)
    # The certificate is checked feature by feature and pattern by pattern.
    # Its validity therefore does not require the LP or the orbit argument.
    balance=[t if len(f)==1 else 0 for f in features]
    numerator=D*base+t*need
    for b,group in classes.items():
        cs=local[group[0]];assert len(cs)==len(W[b]);weights=dict(zip(cs,W[b]))
        for i in group:
            ids,patterns=models[i];literal=[weights[k] for k in roles[i]]
            for j,w in zip(ids,literal):balance[j]+=w
            numerator+=max(sum(literal[j] for j in on) for on in patterns)
    numerator+=sum(max(0,D*costs[c]-actual) for c,actual in zip(colors,balance))
    return dict(fixed=sorted(fixed),size=size,max_edges=numerator//D,numerator=numerator,
                feature_classes=n,block_classes=len(classes),certificate=cert)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("population",type=int);p.add_argument("start",type=int)
    p.add_argument("stop",type=int);p.add_argument("--replay",action="store_true");a=p.parse_args()
    rows=json.loads(Path("seven-deletion-classes.json").read_bytes())[str(a.population)]
    for i in range(a.start,min(a.stop,len(rows))):
        file=Path(f"forest-role-weight-{a.population}-{i}.json")
        cert=json.loads(file.read_bytes())["certificate"] if a.replay else None
        r=bound(set(rows[i]["forest"]),117,cert)
        if a.replay:assert r==json.loads(file.read_bytes())
        else:save(file,r)
        print(i,r["max_edges"],r["feature_classes"],r["block_classes"],flush=True)
