"""Lift a Q7 walk to Q9 by selecting an arbitrary induced square path per visit."""
from itertools import combinations
from random import Random
from collections import defaultdict,Counter
import json,sys
from pysat.solvers import Minicard

def check(p):
    return len(p)==len(set(p)) and min(p)>=0 and max(p)<512 and all(((a^p[j]).bit_count()==1)==(i+1==j) for i,a in enumerate(p) for j in range(i+1,len(p)))

def lift(p,target,cap,hint=None):
    n=len(p); assert p[0]==0 and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    occ=[[4*i+c+1 for c in range(4)] for i in range(n)]
    port=[[4*n+4*i+c+1 for c in range(4)] for i in range(n+1)]
    by=defaultdict(list)
    for i,v in enumerate(p):by[v].append(i)
    parity=[[],[]]
    with Minicard() as sat:
        for row in port:
            sat.add_clause(row);sat.add_atmost(row,1)
        sat.add_clause([port[0][0]])
        for i,o in enumerate(occ):
            a,b=port[i:i+2]
            sat.add_atmost(o,3)
            for u in range(4):
                parity[(p[i].bit_count()+u.bit_count())%2].append(o[u])
                sat.add_clause([-a[u],o[u]]);sat.add_clause([-b[u],o[u]])
                for v in range(4):
                    if u^v==3:
                        sat.add_clause([-a[u],-b[v],o[u^1],o[u^2]])
                    else:
                        for c in range(4):
                            if c!=u and c!=v:sat.add_clause([-a[u],-b[v],-o[c]])
            if i:
                for c in range(4):sat.add_clause([-occ[i-1][c],-o[c],port[i][c]])
        for v,rows in by.items():
            for i,j in combinations(rows,2):
                for c in range(4):
                    for d in (c,c^1,c^2):sat.add_clause([-occ[i][c],-occ[j][d]])
            for k in range(7):
                u=v^(1<<k)
                if u<v or u not in by:continue
                for i in rows:
                    for j in by[u]:
                        if abs(i-j)>1:
                            for c in range(4):sat.add_clause([-occ[i][c],-occ[j][c]])
        for group,minimum in zip(parity,((target+2)//2,(target+1)//2)):
            if minimum>len(group):return "UNSAT",None
            sat.add_atmost([-x for x in group],len(group)-minimum)
        if hint:
            phase=[]
            for i,layer in enumerate(hint):
                phase.extend([port[i][layer[0]],port[i+1][layer[-1]]]);phase.extend(occ[i][x] if x in layer else -occ[i][x] for x in range(4))
            sat.set_phases(phase)
        sat.conf_budget(cap);ok=sat.solve_limited()
        if ok is not True:return ("UNKNOWN" if ok is None else "UNSAT"),None
        model=set(sat.get_model());out=[]
        for i,v in enumerate(p):
            a=next(c for c in range(4) if port[i][c] in model);b=next(c for c in range(4) if port[i+1][c] in model)
            out.append(v+128*a)
            if a^b==3:
                [c]=[c for c in (a^1,a^2) if occ[i][c] in model]
                out.append(v+128*c)
            if a!=b:out.append(v+128*b)
        assert len(out)>=target+1 and check(out)
        return "FOUND",out

def projections(seq):
    for a,b in combinations(range(9),2):
        labels={};p=[0];hint=[[0]]
        for x in seq:
            if x in (a,b):hint[-1].append(hint[-1][-1]^(1 if x==a else 2))
            else:
                p.append(p[-1]^(1<<labels.setdefault(x,len(labels))));hint.append([hint[-1][-1]])
        yield p,hint
def records(filename):
    from pathlib import Path
    path=Path(filename)
    if path.suffix==".csv":
        import csv
        with path.open() as stream:
            for row in csv.DictReader(stream):
                if int(row["n"])==9:
                    yield list(map(int,row["actions"].split()))
    elif path.suffix==".json":
        for row in json.loads(path.read_text()):
            vertices=row["vertex_sequence"]
            assert check(vertices)
            yield [(x^y).bit_length()-1 for x,y in zip(vertices,vertices[1:])]
    else:
        with path.open() as stream:
            for ln in stream:
                d,*seq=map(int,ln.split())
                if d==9: yield seq

if __name__=="__main__":
    target,cap,lim=map(int,sys.argv[1:4]);walks={}
    if len(sys.argv)!=5:raise SystemExit("usage: script EDGES CONFLICT_BUDGET MAX_SKELETONS PUBLIC_BANK_FILE")
    for seq in records(sys.argv[4]):
        for p,hint in projections(seq):walks.setdefault(bytes(p),hint)
    data=list(walks.items());Random(8550).shuffle(data)
    for p,hint in data[:lim]:
        st,out=lift(p,target,cap,hint)
        print(json.dumps([st,p.hex(),out],separators=(",",":")),flush=True)
        if out:break
