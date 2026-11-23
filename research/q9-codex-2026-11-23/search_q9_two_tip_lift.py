"""Two crossings of the ninth coordinate, one at each tip of a prescribed Q8 snake."""
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
from io import StringIO
import json,random,subprocess,sys,os
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from verify_q8_free_layer_dual import is_forest
from verify_q9_center_avoidance import forms,verify

def build(arm,ep,goal,axes):
    roots={arm[0],arm[-1]}
    free=set(range(256))-set(arm[1:-1])
    own={};tables=[];rows={};rhs=[]
    delta=len(arm)%2+(1 if ep==0 else -1)
    def row(key,value=0):
        if key not in rows:rows[key]=len(rhs);rhs.append(value)
        return rows[key]
    re=row("ends",2);rp=row("parity",delta)
    for v in sorted(free):
        nbr=[v^(1<<i) for i in range(8) if v^(1<<i) in free]
        same=(v^arm[0]).bit_count()%2==ep
        options=[];own[v]={};scope=[v,*nbr]
        if v not in roots:options.append((0,1,0,{}))
        for degree in range(3):
            total=degree+int(v in roots)
            if total!=2 and not (total==1 and same):continue
            for ns in combinations(nbr,degree):
                incident=sum(v^w for w in ns)
                on=1+sum(1<<(j+1) for j,w in enumerate(nbr) if w in ns)
                coeff={rp:1 if (v^arm[0]).bit_count()%2==0 else -1}
                if total==1:coeff[re]=1
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
    const=2*y[re]+delta*y[rp]
    factors=[]
    for scope,options in tables:
        vals=sorted(((on,off,value*scale-sum(a*y[r] for r,a in co.items())) for on,off,value,co in options),key=lambda t:-t[2])
        factors.append((scope,vals))
    weights=[[r[0],r[1],r[2],y[j]] for r,j in rows.items() if isinstance(r,tuple) and isinstance(r[0],int) and y[j]]
    cert=dict(end_weight=y[re],balance_weight=y[rp],weights=weights,axes=axes,scale=scale)
    return const,scale,factors,cert

def work(job):
    i,word,ep,goal=job;arm=[0]
    for c in word:arm.append(arm[-1]^(1<<int(c)))
    verify(arm);assert goal%2==0
    target=goal+1-len(arm)
    axes=list(combinations(range(8),3));random.Random(314).shuffle(axes)
    built=build(arm,ep,goal,axes[:int(os.environ.get("Q9_TWO_TIP_PARTS","8"))])
    if built is None:return [i,ep,goal,"EMPTY_FACTOR",None,None]
    constant,scale,factors,certificate=built
    upper=constant+sum(o[0][2] for _,o in factors)
    if upper<target*scale:return [i,ep,goal,"DUAL_EXCLUSION",upper,None]
    out=StringIO()
    print(i,target,arm[0],scale,constant,upper,len(arm),*arm,len(factors),file=out)
    for scope,opts in factors:
        print(len(scope),*scope,len(opts),file=out)
        for t in opts:print(*t,file=out)
    l=subprocess.check_output([os.environ.get("Q9_TWO_TIP_SOLVER","/tmp/q8_two_tips_dual20"),os.environ.get("Q9_TWO_TIP_CAP","120000"),"two"+str(ep)],input=out.getvalue(),text=True).split()
    rid,st,nodes,*raw=l;assert int(rid)==i
    w=None
    if st=="FOUND":
        w=list(map(int,raw));verify(w)
        assert len(w)==goal+1 and {v for v in w if v<256}==set(arm)
        assert {v for v in arm if 256+v in w}=={arm[0],arm[-1]} and (w[0]^arm[0]^256).bit_count()%2==ep
    return [i,ep,goal,st,upper,w]
if __name__=="__main__":
    filename=sys.argv[1] if len(sys.argv)>1 else "q8_exchange_new_rooted_arms.txt"
    uniq={};words=sorted(open(filename).read().split(),key=lambda s:(-len(s),s))
    for w in words:
        p=[0]
        for c in w:p.append(p[-1]^1<<int(c))
        uniq.setdefault(forms(p,len(w))[0],w)
    anchors=list(uniq.values())
    c=next(w for w in anchors if len(w)%2==0)
    control=work((-1,c,0,len(c)+2));assert control[3]=="FOUND";print(json.dumps(control),flush=True)
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(work,((i,w,colour,192) for i,w in enumerate(anchors) for colour in (0,1)),chunksize=1):
            print(json.dumps(r),flush=True)
            if r[-1]:break
