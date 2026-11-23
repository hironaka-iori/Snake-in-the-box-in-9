"""Search the low-contact exterior without anchoring old vertices, using face inequalities."""
import json,sys,random,os
from itertools import combinations
from concurrent.futures import ProcessPoolExecutor
from io import StringIO
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from verify_q8_free_layer_dual import is_forest
from verify_q9_center_avoidance import verify,forms
import gzip,subprocess
def parents():
    out={}
    for l in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,l.split()))
        if len(p)==192:out.setdefault(forms(p,191)[0],p)
    return list(out.values())

def build(p,r,ep,goal,fixed=None,domain=None):
    old=set(p);D={x for x in range(512) if x in old or sum((x^1<<d) in old for d in range(9))<=r}
    if domain is not None:D=set(domain)
    fixed=set() if fixed is None else set(fixed)
    axes=list(combinations(range(9),3));random.Random(9182).shuffle(axes);axes=axes[:int(os.environ.get("Q9_SHELL_PARTS","10"))]
    groups=[];master={};index={};rhs=[]
    def row(key,val=0):
        if key not in index:index[key]=len(rhs);rhs.append(val)
        return index[key]
    end=row("end",2);delta=(1 if ep==0 else -1) if goal%2==0 else 0;bal=row("bal",delta)
    for v in sorted(D):
        dirs=[1<<i for i in range(9) if v^1<<i in D];scope=[v]+[v^d for d in dirs];options=[(0,1,0,{})];master[v]={}
        if v in fixed:options.clear()
        required={m for m in dirs if v^m in fixed}
        for d in (1,2):
            if d==1 and goal%2==0 and v.bit_count()%2!=ep:continue
            for edges in combinations(dirs,d):
                if not required.issubset(edges):continue
                co={bal:1 if v.bit_count()%2==0 else -1}
                if d==1:co[end]=1
                master[v][sum(edges)]=co
                on=1+sum(1<<(i+1) for i,x in enumerate(dirs) if x in edges)
                options.append((on,(1<<len(scope))-1-on,1,co))
        if not options:return None
        groups.append((scope,options))
    for ax in axes:
        dr=[1<<j for j in ax];m=sum(dr)
        for base in range(512):
            if base&m:continue
            scope=sorted(v for v in D if v&~m==base)
            if not scope:continue
            ix={}
            for v in scope:
                for z,co in master[v].items():
                    i=row((m,v,z&m));co[i]=-1;ix[v,z&m]=i
            opts=[]
            for on in range(1<<len(scope)):
                picked={v for j,v in enumerate(scope) if on>>j&1}
                if not fixed.intersection(scope)<=picked or not is_forest(picked,dr):continue
                sig=[(v,sum(d for d in dr if v^d in picked)) for v in picked]
                if all(s in ix for s in sig):
                    opts.append((on,((1<<len(scope))-1)^on,0,{ix[s]:1 for s in sig}))
            if not opts:return None
            groups.append((scope,opts))
    I=[];J=[];V=[];c=[]
    for gi,(scope,opts) in enumerate(groups):
        gid=row(("g",gi),1)
        for on,off,val,co in opts:
            j=len(c);c.append(val)
            for i,v in co.items():I.append(i);J.append(j);V.append(v)
            I.append(gid);J.append(j);V.append(1)
    mat=coo_matrix((V,(I,J)),shape=(len(rhs),len(c))).tocsc()
    sol=linprog(-np.array(c),A_eq=mat,b_eq=rhs,bounds=(0,None),method="highs",options={"threads":1,"time_limit":30})
    scale=10000;y=[round(float(-v)*scale) for v in sol.eqlin.marginals] if sol.success else [0]*len(rhs)
    const=2*y[end]+delta*y[bal];out=[]
    for scope,opts in groups:
        values=sorted(((a,b,val*scale-sum(y[i]*v for i,v in co.items())) for a,b,val,co in opts),key=lambda t:-t[2])
        out.append((scope,values))
    bound=const+sum(opts[0][2] for _,opts in out)
    certificate={"scale":scale,"end":y[end],"balance":y[bal],"axes":axes,
                 "weights":[[m,v,z,y[j]] for key,j in index.items()
                 if isinstance(key,tuple) and len(key)==3 and y[j] for m,v,z in [key]]}
    return D,bound,const,out,certificate
def solve(job):
    i,p,r,ep,g,cap,*spec=job;built=build(p,r,ep,g,*spec)
    if built is None:return [i,r,ep,g,'EMPTY_FACTOR',None,None]
    D,bound,const,out,certificate=built
    cert_dir=os.environ.get("Q9_SHELL_CERT_DIR")
    if cert_dir:
        with open(f"{cert_dir}/r{r}_goal{g}_parent{i}_e{ep}.json","w") as f:
            json.dump({"parent":p,"threshold":r,"goal":g,"end_colour":ep,"upper":bound,**certificate},f,separators=(",",":"))
    if bound<(g+1)*10000:return [i,r,ep,g,"DUAL_EXCLUSION",bound,None]
    stream=StringIO()
    print(i,g+1,ep,10000,const,bound,len(D),*sorted(D),len(out),file=stream)
    for scope,opts in out:
        print(len(scope),*scope,len(opts),file=stream)
        for a,b,val in opts:print(a,b,val,file=stream)
    raw=subprocess.check_output([os.environ.get("Q9_SHELL_SOLVER","/tmp/q9_shell_factor20"),str(cap)],input=stream.getvalue(),text=True).split()
    idx,st,nn,*w=raw;assert int(idx)==i
    if w:
        w=list(map(int,w));verify(w);assert set(w)<=D
        if os.getenv('Q9_PATH_MINIMUM'):
            assert len(w)>=g+1 and (len(w)-g-1)%2==0
            if g%2==0:assert w[0].bit_count()%2==ep
        else:assert len(w)==g+1
        if spec:assert set(spec[0])<=set(w)
    return [i,r,ep,g,st,bound,w or None]
if __name__=="__main__":
    bank=parents()
    # Prefixes of real 191 snakes have 190 edges and known matching endpoint color.
    controls=[(i,bank[i],1,bank[i][0].bit_count()%2,190,350000) for i in (0,42,76)]
    level=int(sys.argv[1]) if len(sys.argv)>1 else 2
    jobs=controls+[(i,p,level,e,192,240000) for i,p in enumerate(bank) for e in (0,1)]
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(solve,jobs,chunksize=1):
            assert r[3]!=190 or r[4] in ("FOUND","UNKNOWN")
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[4]=="FOUND" and r[3]>=192:break
