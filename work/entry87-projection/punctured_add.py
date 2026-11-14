"""All one-address enlargements and contractions of fixed Q8 bank projections."""
from collections import Counter
from math import comb
from pathlib import Path
import argparse,json
from punctured_pit import groups,examine
from solve import save


def possible(sites):
    graph={v:{v^(1<<b) for b in range(8)}&sites for v in sites}
    D={v for v,g in graph.items() if len(g)<=2}
    k=193-len(sites)
    if len(D)<k:return "degree capacity",None
    leaves={v for v,g in graph.items() if len(g)<2}
    if any(not graph[v] for v in leaves) or len(leaves)>2:return "projected endpoint degree",None
    # Let a projected lift use k doubled vertices. Adjacent double columns
    # fill a square. In any matching of the subgraph on their candidate set,
    # at least one endpoint per edge must therefore stay single.
    matching=[];used=set()
    for x in sorted(D,key=lambda v:len(graph[v]&D)):
        if x in used:continue
        for y in sorted((graph[x]&D)-used):
            matching.append((x,y));used.add(x);used.add(y);break
    if len(D)-len(matching)<k:return "matching capacity",None
    # Every projected trace is itself a simple Hamilton path. In a bipartite
    # Q8 its two color classes therefore differ by at most one.
    n_even=sum(v.bit_count()%2==0 for v in sites)
    if abs(2*n_even-len(sites))>1:return "projected parity",None
    return None,(len(D),len(matching))


def run(a):
    g=groups();memo={};rows=[];find=None;test=a.action=="test"
    for i in range(a.start,min(a.stop,len(g))):
        P,orig=g[i];S=set(P);counts=Counter();cases=[]
        for x in range(256):
            if (x in S)!=a.remove:continue
            sites=S^{x}
            reason,n=possible(sites)
            if reason:counts[reason]+=1;continue
            code=tuple(sorted(sites))
            if code in memo:
                counts["duplicate"]+=1;continue
            memo[code]=(i,x)
            if test:
                r=examine(code,f"change-{int(a.remove)}-{i}-{x}",a.budget)
                counts[r["status"]]+=1
                if r["status"] in ("FOUND","OPEN"):
                    cases.append(dict(x=x,**r))
                if r.get("witness"):find=r["witness"];break
            else:
                counts["survives"]+=1;cases.append(x)
        rows.append(dict(index=i,counts=counts,candidates=cases))
        if find:break
    file=Path(f"punctured-{'remove' if a.remove else 'add'}-{a.action}-{a.start}-{a.stop}.json")
    save(file,rows)
    print(len(rows),sum((Counter(x["counts"]) for x in rows),Counter()),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("action",choices=("screen","test"));p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--remove",action="store_true");p.add_argument("--budget",type=int,default=30000)
    run(p.parse_args())
