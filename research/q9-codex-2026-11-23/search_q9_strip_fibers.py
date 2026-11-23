"""Add all Q4 strip shape tables to the unrestricted Q3-fiber solver."""
import sys,json
from collections import defaultdict
from functools import lru_cache
from pysat.solvers import Minicard
import search_q9_cube_fiber_lift as lifting
from q9_projection_strip_bounds import catalogue,signatures,pattern
@lru_cache(None)
def split_masks(signature):
    left=defaultdict(set);right=defaultdict(set)
    for m in catalogue().get(signature,[]):
        a,b=m&255,m>>8
        left[a].add(b);right[b].add(a)
    return left,right
@lru_cache(None)
def domain(k):
    return frozenset(m for m in range(256) if (q:=pattern(m)) is not None and len(q)==k)
def install(sat,p,target):
    n=len(p);last=8*n+8*(n+1)
    def fresh():
        nonlocal last
        last+=1;return last
    visits=defaultdict(list)
    for i,v in enumerate(p):visits[v].append(i)
    domains=[domain(len(visits[v])) for v in range(64)]
    strips=list(signatures(p))
    changed=True
    while changed:
        changed=False
        for u,v,d,sig in strips:
            l,r=split_masks(sig)
            for a,b,side in ((u,v,l),(v,u,r)):
                old=domains[a]
                domains[a]={m for m in old if side.get(m,set()) & domains[b]}
                changed |= len(old)!=len(domains[a])
                if not domains[a]:
                    sat.add_clause([]);return
    variables=[];total_slots=[]
    for v,dom in enumerate(domains):
        y={m:fresh() for m in sorted(dom)};variables.append(y)
        sat.add_clause(list(y.values()))
        if not visits[v]:continue
        z=[fresh() for _ in range(8)]
        for c in range(8):
            os=[8*i+c+1 for i in visits[v]]
            for o in os:sat.add_clause([-o,z[c]])
            sat.add_clause([-z[c],*os])
        lim=max(m.bit_count() for m in dom)
        t=[fresh() for _ in range(lim)];total_slots+=t
        for a,b in zip(t,t[1:]):sat.add_clause([-b,a])
        for m,h in y.items():
            for c in range(8):sat.add_clause([-h,z[c] if m>>c&1 else -z[c]])
            k=m.bit_count()
            if k:sat.add_clause([-h,t[k-1]])
            if k<lim:sat.add_clause([-h,-t[k]])
    if len(total_slots)<target+1:sat.add_clause([]);return
    sat.add_atmost([-x for x in total_slots],len(total_slots)-target-1)
    for u,v,d,sig in strips:
        l,r=split_masks(sig)
        for a,b,side in ((u,v,l),(v,u,r)):
            if len(domains[b])==1:continue
            for m,h in variables[a].items():
                allowed=side[m]&domains[b]
                if len(allowed)!=len(domains[b]):
                    sat.add_clause([-h,*[variables[b][k] for k in sorted(allowed)]])
def solve(p,target,cap):
    class WithStrips(Minicard):
        def __init__(self):
            super().__init__();install(self,p,target)
    previous=lifting.Minicard
    try:
        lifting.Minicard=WithStrips
        return lifting.fiber_solve(p,3,target,cap)
    finally:
        lifting.Minicard=previous
if __name__=='__main__':
    target,cap=int(sys.argv[2]),int(sys.argv[3])
    for r in map(json.loads,open(sys.argv[1])):
        if r[0]=='UNKNOWN':
            status,path=solve(bytes.fromhex(r[1]),target,cap)
            print(json.dumps([status,r[1],path],separators=(',',':')),flush=True)
            if path:break
