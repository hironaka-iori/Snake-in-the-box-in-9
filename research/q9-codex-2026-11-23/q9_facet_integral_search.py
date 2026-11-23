"""Search integer assignments in the face relaxation and cut whole induced cycles."""
import json,time,sys
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix, hstack, vstack, csr_matrix
from scipy.optimize import Bounds, LinearConstraint, milp
from q9_facet_bank_dual import build,families

def components(s):
    remain=set(s);out=[]
    while remain:
        seq=[remain.pop()]
        for x in seq:
            grow={x^(1<<d) for d in range(9)}&remain
            seq.extend(grow);remain-=grow
        out.append(seq)
    return out

def solve(word,axes,target,wall,global_hint=()):
    mat,obj,nr,factors,inside,tips,pool=build(word,axes,export=True)
    z=mat.shape[1];m=len(pool);ix={v:j for j,v in enumerate(pool)}
    mat=hstack([mat,csr_matrix((mat.shape[0],m))],format="csr")
    rr=[];cc=[];vv=[];offset=0
    for row,v in enumerate(pool):
        for k,(value,_) in enumerate(factors[row]):
            if value:rr.append(row);cc.append(offset+k);vv.append(1)
        offset+=len(factors[row])
        rr.append(row);cc.append(z+row);vv.append(-1)
        rr.append(m);cc.append(z+row);vv.append(1)
    mat=vstack([mat,coo_matrix((vv,(rr,cc)),shape=(m+1,z+m))],format="csr")
    cost=np.zeros(z+m)
    if global_hint:
        for v in pool:cost[z+ix[v]]= -1 if v in global_hint else 1
    integer=np.zeros(z+m);integer[z:]=1
    results=[]
    for majority in ((0,1) if target%2==0 else (None,)):
        now=time.monotonic();delta=(0 if majority is None else 1-2*majority)-sum(1-2*(v.bit_count()%2) for v in inside)
        counts=[1,1] if majority is None else [2*(majority==p) for p in (0,1)]
        rhs=counts+[delta]+[0]*(nr-3)+[1]*len(factors)+[0]*m+[target+1-len(inside)]
        constraints=[LinearConstraint(mat,rhs,rhs)]
        cuts=0;out=dict(majority=majority,status="UNKNOWN")
        while (left:=wall-(time.monotonic()-now))>.01:
            s=milp(c=cost,integrality=integer,bounds=Bounds(0,1),constraints=constraints,options={"time_limit":left,"threads":1})
            if s.x is None:
                out["solver_message"]=s.message
                if s.status==2:out["status"]="MILP_INFEASIBLE"
                break
            occ=inside|{v for v,val in zip(pool,s.x[z:]) if val>.5}
            assert len(occ)==target+1 and tips<=occ
            deg={v:sum(v^(1<<j) in occ for j in range(9)) for v in occ}
            assert set(deg.values())<={1,2} and sum(i==1 for i in deg.values())==2
            groups=components(occ)
            if len(groups)==1:
                path=[next(v for v in occ if deg[v]==1)]
                while len(path)<len(occ):
                    last=path[-2] if len(path)>1 else -1
                    v,={path[-1]^(1<<j) for j in range(9)}&occ-{last};path.append(v)
                assert len(path)==len(set(path)) and all(((v^u).bit_count()==1)==(j+1==i) for i,v in enumerate(path) for j,u in enumerate(path[:i]))
                out.update(status="FOUND",vertices=path);break
            for g in groups:
                if all(deg[v]==2 for v in g):
                    pos=[z+ix[v] for v in g if v not in inside]
                    row=csr_matrix(([1]*len(pos),([0]*len(pos),pos)),shape=(1,z+m))
                    constraints.append(LinearConstraint(row,-np.inf,len(pos)-1));cuts+=1
        out.update(cuts=cuts,seconds=round(time.monotonic()-now,2));results.append(out)
        if out["status"]=="FOUND":break
    return results

if __name__=="__main__":
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    if sys.argv[1]=="control":
        p=json.loads(Path("q8_catalogue_lifts_verified.json").read_text())["lower_certificate"]["vertices"]
        slices=[];q=[]
        for v in p:
            if q and v>>8!=q[-1]>>8:slices.append(q);q=[]
            q.append(v)
        slices.append(q);a=max(slices,key=len)
        w="".join(str((v^u).bit_length()-1) for v,u in zip(a,a[1:]))
        hint={v^a[0] for v in p}
        print(json.dumps(solve(w,families(3),191,12,hint)),flush=True)
    else:
        number,wall=map(int,sys.argv[1:3])
        for i in map(int,sys.argv[3:]):
            print(json.dumps(dict(i=i,r=solve(bank[i],families(number),192,wall))),flush=True)
