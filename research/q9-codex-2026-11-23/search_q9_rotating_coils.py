"""Look for a longer snake by opening a rotation-invariant induced cycle."""
from itertools import combinations
from collections import Counter,defaultdict
from concurrent.futures import ProcessPoolExecutor
from math import lcm
from pathlib import Path
from pysat.solvers import Minicard
import json
from verify_q9_center_avoidance import verify
def partitions(n,lo=1):
    if not n:yield ();return
    for a in range(lo,n+1):
        for r in partitions(n-a,a):yield (a,)+r
def types(dim):
    return sorted({tuple(sorted((a,int(bool(b>>i&1))) for i,a in enumerate(t)))
                   for t in partitions(dim) for b in range(1<<len(t))})
def order(cls):return lcm(*(d*(1+s) for d,s in cls))
def graph(cls):
    dim=sum(d for d,_ in cls);n=1<<dim;perm=[];flip=0
    for size,neg in cls:
        j=len(perm);perm.extend(j+(i+1)%size for i in range(size));flip|=neg<<j
    image=[flip^sum(1<<v for i,v in enumerate(perm) if x>>i&1) for x in range(n)]
    assert sorted(image)==list(range(n))
    owner=[-1]*n;orbits=[]
    for x in range(n):
        if owner[x]>=0:continue
        y=x;a=[]
        while owner[y]<0:
            owner[y]=len(orbits);a.append(y);y=image[y]
        assert x==y
        orbits.append(a)
    d=order(cls);allowed={i for i,o in enumerate(orbits) if len(o)==d}
    adj={i:Counter(owner[orbits[i][0]^(1<<k)] for k in range(dim)) for i in allowed}
    return dim,orbits,owner,allowed,adj

def enumerate_cls(args):
    cls,goal,cap=args
    dim,orb,own,allowed,adj=graph(cls);d=order(cls)
    if goal%d or goal//d>len(allowed):return [cls,goal,"SIZE",0,None]
    with Minicard() as s:
        k=goal//d
        # In a longer cycle a selected vertex has exactly two selected neighbors.
        # Orbits adjacent internally to themselves count on the same footing.
        for i in allowed:
            near=list(j for j in adj[i] if j in allowed and j!=i)
            need=2-adj[i].get(i,0)
            weights={j:adj[i][j] for j in near}
            if need<0:s.add_clause([-i-1]);continue
            # Native cardinality is used only with distinct literals.
            if all(w==1 for w in weights.values()):
                for group in combinations(near,need+1):s.add_clause([-i-1]+[-j-1 for j in group])
                if len(near)<need:s.add_clause([-i-1])
                else:
                    for group in combinations(near,len(near)-need+1):s.add_clause([-i-1]+[j+1 for j in group])
            else:
                for mask in range(1<<len(near)):
                    if sum(weights[j] for a,j in enumerate(near) if mask>>a&1)==need:continue
                    s.add_clause([-i-1]+[-j-1 if mask>>a&1 else j+1 for a,j in enumerate(near)])
        s.add_atmost([i+1 for i in allowed],k)
        s.add_atmost([-i-1 for i in allowed],len(allowed)-k)
        rejected=0
        while True:
            remain=cap-s.accum_stats()["conflicts"]
            if remain<=0:return [cls,goal,"UNKNOWN",rejected,None]
            s.conf_budget(remain);ok=s.solve_limited()
            if ok is not True:return [cls,goal,"UNSAT" if ok is False else "UNKNOWN",rejected,None]
            model=set(s.get_model());verts={x for i in allowed if i+1 in model for x in orb[i]}
            assert len(verts)==goal
            unseen=verts.copy();parts=[]
            while unseen:
                start=min(unseen);p=[start];last=-1
                while True:
                    end=p[-1]
                    nb=sorted(end^(1<<b) for b in range(dim) if end^(1<<b) in verts)
                    assert len(nb)==2
                    nxt=next(v for v in nb if v!=last)
                    if nxt==start:break
                    p.append(nxt);last=end
                unseen.difference_update(p);parts.append(p)
            if len(parts)==1:
                cycle=parts[0];verify(cycle[:-1])
                assert (cycle[0]^cycle[-1]).bit_count()==1 and all((v^cycle[-1]).bit_count()!=1 for v in cycle[1:-2])
                return [cls,goal,"FOUND",rejected,cycle]
            rejected+=1
            for p in parts:s.add_clause([-i-1 for i in {own[v] for v in p}])
def brute(cls):
    dim,orb,own,allowed,adj=graph(cls)
    yes=set();n=1<<dim
    for mask in range(1,1<<len(allowed)):
        vs={v for j,i in enumerate(sorted(allowed)) if mask>>j&1 for v in orb[i]}
        ns={v:[v^(1<<b) for b in range(dim) if v^(1<<b) in vs] for v in vs}
        if any(len(q)!=2 for q in ns.values()):continue
        stack=[min(vs)];reached=set(stack)
        for x in stack:
            for u in ns[x]:
                if u not in reached:stack.append(u);reached.add(u)
        if len(reached)==len(vs):yes.add(len(vs))
    return yes
if __name__=="__main__":
    control=Counter()
    for cls in types(4):
        if order(cls)<2:continue
        exact=brute(cls)
        for g in range(4,17,2):
            ans=enumerate_cls((cls,g,50000));assert (ans[2]=="FOUND")==(g in exact) and ans[2]!="UNKNOWN"
            control[ans[2]]+=1
    print(json.dumps(dict(controls=control)),flush=True)
    tasks=sorted(((c,g,40000) for c in types(9) if order(c)>=3 for g in range(194,209,2) if g%order(c)==0),
                 key=lambda t:(-order(t[0]),t[1],t[0]))
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(enumerate_cls,tasks,buffersize=24,chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
