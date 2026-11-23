"""Exact rooted lift of fixed base walk, with unrestricted traversal in each fiber."""
import sys,time,json,csv
from itertools import combinations
from collections import defaultdict
from random import Random
from pysat.solvers import Minicard

def verify(p):
    return len(p)==len(set(p)) and min(p)>=0 and max(p)<512 and all(((a^p[j]).bit_count()==1)==(i+1==j) for i,a in enumerate(p) for j in range(i+1,len(p)))
def fiber_solve(p,d,target,cap,hint=None):
    n=len(p);m=1<<d;shift=9-d
    assert p[0]==0 and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    O=[[i*m+c+1 for c in range(m)] for i in range(n)]
    P=[[n*m+i*m+c+1 for c in range(m)] for i in range(n+1)]
    N=[[c^(1<<a) for a in range(d)] for c in range(m)]
    by=defaultdict(list); groups=[[],[]]
    for i,v in enumerate(p):by[v].append(i)
    with Minicard() as sat:
        for row in P:
            sat.add_clause(row);sat.add_atmost(row,1)
        sat.add_clause([P[0][0]])
        for i,row in enumerate(O):
            for c,h in enumerate(row):
                e=P[i][c];f=P[i+1][c]
                sat.add_clause([-e,h]);sat.add_clause([-f,h])
                if i:sat.add_clause([-O[i-1][c],-h,e])
                slots=[row[z] for z in N[c]]+[e,f]
                for a,b,k in combinations(slots,3):sat.add_clause([-h,-a,-b,-k])
                for j in range(len(slots)):sat.add_clause([-h,*slots[:j],*slots[j+1:]])
                groups[(p[i].bit_count()+c.bit_count())%2].append(h)
            # Squares cannot be present anywhere in a legitimate fiber path.
            for u in range(m):
                for a,b in combinations(range(d),2):
                    ma=1<<a;mb=1<<b
                    if not u&(ma|mb):
                        sat.add_clause([-row[v] for v in (u,u^ma,u^mb,u^ma^mb)])
        if d<=3:
            last=m*(2*n+1);bits=[]
            for i in range(n+1):
                row=[]
                for dim in range(d):
                    last+=1;bit=last;row.append(bit)
                    for val in (0,1):
                        sat.add_clause([(-bit if val else bit), *[P[i][c] for c in range(m) if ((c>>dim)&1)==val]])
                bits.append(row)
            for dim in range(d-1):
                last+=1;eq=last;sat.add_clause([eq])
                for row in bits[1:]:
                    x,y=row[dim:dim+2];last+=1;new=last
                    sat.add_clause([-eq,x,-y])
                    for cl in ([-new,eq],[-new,-x,y],[-new,x,-y],[-eq,x,y,new],[-eq,-x,-y,new]):
                        sat.add_clause(cl)
                    eq=new
            score=[]
            for i in range(n):
                for a,b in zip(bits[i],bits[i+1]):
                    last+=1;t=last;score.append(t)
                    for cl in ([-a,-b,-t],[a,b,-t],[a,-b,t],[-a,b,t]):sat.add_clause(cl)
                if d==3:
                    last+=2;t=last-1;z=last;score.extend([t,z]);sat.add_clause([-t,z]);sat.add_clause([t,-z])
                    for a in range(m):
                        for b in range(m):
                            prefix=[-P[i][a],-P[i+1][b]];diff=a^b;h=diff.bit_count()
                            if h!=2:sat.add_clause([*prefix,-t])
                            if h<=1:
                                for c in range(m):
                                    if c not in (a,b):sat.add_clause([*prefix,-O[i][c]])
                            if h==2:
                                other=[O[i][c] for c in range(m) if (a^c)&(7^diff)]
                                sat.add_clause([*prefix,-t,*other])
                                for q in other:sat.add_clause([*prefix,-q,t])
            k=target-(n-1)
            if k>len(score):return "UNSAT",None
            if k>0:sat.add_atmost([-x for x in score],len(score)-k)
        for v,ids in by.items():
            for i,j in combinations(ids,2):
                for c in range(m):
                    for b in [c,*N[c]]:sat.add_clause([-O[i][c],-O[j][b]])
            for a in range(shift):
                u=v^(1<<a)
                if u<v or u not in by:continue
                for i in ids:
                    for j in by[u]:
                        if abs(i-j)>1:
                            for c in range(m):sat.add_clause([-O[i][c],-O[j][c]])
        for l,t in zip(groups,((target+2)//2,(target+1)//2)):
            if len(l)<t:return "UNSAT",None
            sat.add_atmost([-h for h in l],len(l)-t)
        if hint:
            phase=[]
            for i,l in enumerate(hint):
                phase.extend([P[i][l[0]],P[i+1][l[-1]]]);phase.extend(O[i][c] if c in l else -O[i][c] for c in range(m))
            sat.set_phases(phase)
        while True:
            remain=cap-sat.accum_stats()["conflicts"]
            if remain<=0:return "UNKNOWN",None
            sat.conf_budget(remain);ok=sat.solve_limited()
            if ok is not True:return ("UNKNOWN" if ok is None else "UNSAT"),None
            model=set(sat.get_model());out=[];cuts=0
            for i,v in enumerate(p):
                entry=next(c for c in range(m) if P[i][c] in model)
                end=next(c for c in range(m) if P[i+1][c] in model)
                rem={c for c in range(m) if O[i][c] in model};t=entry
                while True:
                    rem.remove(t);out.append(v+(t<<shift))
                    if t==end:break
                    [t]=set(N[t])&rem
                while rem:
                    x=next(iter(rem));comp={x};stack=[x]
                    while stack:
                        fresh=set(N[stack.pop()])&rem-comp;comp.update(fresh);stack.extend(fresh)
                    rem-=comp;sat.add_clause([-O[i][c] for c in comp]);cuts+=1
            if not cuts:
                assert len(out)>=target+1 and verify(out);return "FOUND",out

def projections(seq,d):
    for removed in combinations(range(9),d):
        ids={};p=[0];hint=[[0]]
        for x in seq:
            if x in removed:hint[-1].append(hint[-1][-1]^(1<<removed.index(x)))
            else:
                p.append(p[-1]^(1<<ids.setdefault(x,len(ids))));hint.append([hint[-1][-1]])
        yield bytes(p),hint

if __name__=="__main__":
    d,target,cap,limit=map(int,sys.argv[1:5]);walks={}
    if len(sys.argv)>5 and sys.argv[5]=="190":
        bank=(list(map(int,r["actions"].split())) for r in csv.DictReader(open("/private/tmp/q9_all190_20261119.csv")))
    else:bank=(list(map(int,ln.split()))[1:] for ln in open("/private/tmp/q9_project_records_input9"))
    for seq in bank:
        for p,hint in projections(seq,d):walks.setdefault(p,hint)
    data=list(walks.items());Random(8550).shuffle(data)
    for p,hint in data[:limit]:
        st,out=fiber_solve(p,d,target,cap,hint)
        print(json.dumps([st,p.hex(),out],separators=(",",":")),flush=True)
        if out:break
