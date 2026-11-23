from pathlib import Path
import itertools,json
from prepare import D,R,majority,NB,graph,parts
from solve import solve,valid
r,m,x,y,b,l,C,cc,demand=map(int,(D/'strong_control.txt').read_text().split())
w=(R/'q9_gap_generations/prior190.words').read_text().splitlines()[r];p=[0]
for z in map(int,w):p.append(p[-1]^(1<<z))
assert valid(p);target=set(p[::2]);A=(target-{l})|{b};adj=graph(A)
ends={v for v in A if len(adj[v])==1};pieces=parts(adj,{C});assert len(parts(adj,set()))==1 and len(pieces)==cc
n=sum(max(len(g&ends),2-min(2,len(set.union(*(adj[v] for v in g))&{C}))) for g in pieces)+int(C in ends);assert demand==n>2
scope=sorted(A-{b,x,y,C})[:20];extra=[v for v in range(512) if v.bit_count()%2==0 and v not in A|NB[m]|{l}][:32]
c=dict(k=1,remove=[b],added=[],ends=[x,y],cut=[C],qs=[m],drop=sorted(set(scope)|{b}),new=sorted(set(extra)|{l}))
st,cuts,conf,path=solve(A,c,100000);assert st=='FOUND' and valid(path) and len(path)==191
print(json.dumps(dict(row=r,mediator=m,separator=C,lower_bound=n,damaged=sorted(A),actual_new=sorted(set(path[::2])-A),witness=path),separators=(',',':')))
