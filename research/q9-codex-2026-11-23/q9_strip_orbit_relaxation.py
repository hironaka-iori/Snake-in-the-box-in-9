"""Upper relaxation for a Q6 projection with Q3 fibers, via adjacent strip types."""
from itertools import permutations
from functools import lru_cache
from collections import defaultdict
import json,sys
import numpy as np
from scipy import sparse
from scipy.optimize import linprog
from q9_projection_strip_bounds import catalogue,signatures,pattern
def symmetry():
    maps=[]
    for perm in permutations(range(3)):
        for offset in (0,3,5,6):
            maps.append([offset^sum(1<<perm[d] for d in range(3) if v>>d&1) for v in range(8)])
    return [min(sum(1<<p[v] for v in range(8) if m>>v&1) for p in maps) for m in range(256)]
orbit=symmetry()
@lru_cache(None)
def allowed(sig):
    return sorted({(orbit[m&255],orbit[m>>8]) for m in catalogue().get(sig,[])})
def solve(p):
    targets=[];objective=[];rows=[];cols=[];vals=[];lookup={}
    dom={v:sorted({orbit[m] for m in range(256) if (k:=pattern(m)) is not None and len(k)==p.count(v)}) for v in range(64)}
    def add(row,col,sign):
        rows.append(row);cols.append(col);vals.append(sign)
    for v,masks in dom.items():
        row=len(targets);targets.append(1)
        for m in masks:
            j=len(objective);lookup[v,m]=j;objective.append(-m.bit_count());add(row,j,1)
    for u,v,d,s in signatures(p):
        opts=allowed(s)
        keys={}
        for w in (u,v):
            for m in dom[w]:
                row=len(targets);targets.append(0);keys[w,m]=row
                add(row,lookup[w,m],-1)
        for a,b in opts:
            j=len(objective);objective.append(0);add(keys[u,a],j,1);add(keys[v,b],j,1)
    A=sparse.coo_matrix((vals,(rows,cols)),shape=(len(targets),len(objective))).tocsr()
    r=linprog(objective,A_eq=A,b_eq=targets,bounds=(0,None),method="highs",options={"threads":1})
    return -r.fun if r.success else None
if __name__=='__main__':
    for r in map(json.loads,open(sys.argv[1])):
        if r[0]=="UNKNOWN":
            print(json.dumps([r[1],solve(bytes.fromhex(r[1]))]),flush=True)
