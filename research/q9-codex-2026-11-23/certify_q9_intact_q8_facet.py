"""Generate rounded duals for every choice of ports and endpoints of one intact Q8 donor."""
from itertools import combinations
from pathlib import Path
import json,random
def build(arm,ports,low,ends,delta,axes):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    from verify_q8_free_layer_dual import is_forest
    roots=set(ports)
    free=set(range(256))-(set(low)-roots)
    own={};tables=[];rows={};rhs=[]
    def row(key,value=0):
        if key not in rows:rows[key]=len(rhs);rhs.append(value)
        return rows[key]
    endrows=[row(("end",h),ends[h]) for h in range(2)];rp=row("parity",delta)
    for v in sorted(free):
        nbr=[v^(1<<i) for i in range(8) if v^(1<<i) in free]
        high=(1+v.bit_count())%2; same=ends[high]>0
        options=[];own[v]={};scope=[v,*nbr]
        if v not in roots:options.append((0,1,0,{}))
        for degree in range(3):
            total=degree+int(v in roots)
            if total!=2 and not (total==1 and same):continue
            for ns in combinations(nbr,degree):
                incident=sum(v^w for w in ns)
                on=1+sum(1<<(j+1) for j,w in enumerate(nbr) if w in ns)
                coeff={rp:1 if (v^arm[0]).bit_count()%2==0 else -1}
                if total==1:coeff[endrows[high]]=1
                own[v][incident]=coeff
                options.append((on,(1<<len(scope))-1-on,1,coeff))
        tables.append((scope,options))
    for directions in axes:
        shifts=[1<<d for d in directions];mask=sum(shifts)
        for b in range(256):
            if b&mask:continue
            scope=sorted(v for v in free if v&~mask==b)
            if not scope:continue
            keys={}
            for v in scope:
                for incident,coeff in own[v].items():
                    inside=incident&mask
                    r=row((mask,v,inside));keys[v,inside]=r;coeff[r]=-1
            opts=[]
            for on in range(1<<len(scope)):
                picked={v for i,v in enumerate(scope) if on&(1<<i)}
                if not roots.intersection(scope)<=picked or not is_forest(picked,shifts):continue
                sig=[(v,sum(s for s in shifts if v^s in picked)) for v in picked]
                if not all(t in keys for t in sig):continue
                opts.append((on,((1<<len(scope))-1)^on,0,{keys[t]:1 for t in sig}))
            tables.append((scope,opts))
    rr=[];cc=[];vv=[];obj=[]
    for i,(_,options) in enumerate(tables):
        group=row(("group",i),1)
        if not options:return None
        for _,_,value,co in options:
            j=len(obj);obj.append(value)
            for r,a in co.items():rr.append(r);cc.append(j);vv.append(a)
            rr.append(group);cc.append(j);vv.append(1)
    A=coo_matrix((vv,(rr,cc)),shape=(len(rhs),len(obj))).tocsc()
    sol=linprog(-np.array(obj,dtype=float),A_eq=A,b_eq=rhs,bounds=(0,None),method="highs",options={"threads":1,"time_limit":45})
    # Even if the LP gives no solution, zero weights are a valid upper bound.
    scale=10000
    y=[round(-float(v)*scale) for v in sol.eqlin.marginals] if sol.success else [0]*len(rows)
    const=sum(a*y[b] for a,b in zip(ends,endrows))+delta*y[rp]
    factors=[]
    for scope,options in tables:
        vals=sorted(((on,off,value*scale-sum(a*y[r] for r,a in co.items())) for on,off,value,co in options),key=lambda t:-t[2])
        factors.append((scope,vals))
    weights=[[r[0],r[1],r[2],y[j]] for r,j in rows.items() if isinstance(r,tuple) and isinstance(r[0],int) and y[j]]
    cert=dict(end_weights=[y[j] for j in endrows],balance_weight=y[rp],weights=weights,axes=axes,scale=scale)
    return const,scale,factors,cert


def configs(arm):
    tips={arm[0],arm[-1]};inside=set(arm)-tips
    spare=sorted(v for v in set(range(256))-set(arm) if all(v^1<<d not in inside for d in range(8)))
    assert spare==[61,144,240] and all((x^y).bit_count()>1 for x,y in combinations(spare,2))
    assert all((x^y).bit_count()>1 for x in tips for y in spare)
    for k in [1,2]:
        for crossing in combinations(sorted(tips),k):
            for size in range(k+1):
                for extras in combinations(spare,size):
                    low=set(arm)|set(extras); lower_ends=(tips-set(crossing))|set(extras)
                    for full in [(2,0),(1,1),(0,2)]:
                        ends=[full[h]-sum(v.bit_count()%2==h for v in lower_ends) for h in range(2)]
                        if min(ends)<0:continue
                        delta=sum((-1)**v.bit_count() for v in low)-(full[0]-full[1])//2
                        yield crossing,extras,full,ends,delta
if __name__=='__main__':
    import sys
    run=build;arm=json.loads(Path('q8_free_layer_full98_duals.jsonl').read_text().splitlines()[0])['certificate']['arm']
    assert arm[0]==0;axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    for crossing,extras,full,ends,delta in configs(arm):
        low=set(arm)|set(extras);ports=set(crossing)|set(extras)
        const,scale,tables,cert=run(arm,ports,low,ends,delta,axes[:int(sys.argv[1])])
        num=const+sum(t[0][2] for _,t in tables);length=len(low)-1+num//scale
        length-=int(length%2!=full[0]%2)
        print(json.dumps(dict(crossing=crossing,extras=extras,full=full,upper_ends=ends,delta=delta,numerator=num,edges_upper=length,cert=cert),separators=(',',':')),flush=True)
