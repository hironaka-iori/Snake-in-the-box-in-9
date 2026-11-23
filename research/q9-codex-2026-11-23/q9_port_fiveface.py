"""Forest density of Q5 subcubes: each path component has at most 14 vertices."""
from itertools import combinations
import gzip,json
from q9_port_edge_degree import build,replay,solve
from q9_overlapping_port_bound import ROOT,NEIGH
from q9_adversarial_port_forests import layouts
from verify_q9_222_disconnected import check,components

def check_q5():
    counts=[0]*33
    def walk(p,used,largest):
        counts[len(p)]+=1
        for d in range(min(5,largest+2)):
            v=p[-1]^(1<<d)
            if v in used or any((u^v).bit_count()==1 for u in p[:-1]):continue
            walk(p+[v],used|{v},max(d,largest))
    walk([0],{0},-1)
    assert max(i for i,c in enumerate(counts) if c)==14
    return counts[14]

def build5(edges):
    nr,n,N,rows=build(edges)
    R={v for e in edges for v in e}
    adj=[R.intersection(ns) for ns in NEIGH]
    sat={v for v in R if len(adj[v])==2}
    free=sorted(v for v in range(512) if v not in R and len(adj[v])<=2 and not adj[v]&sat)
    idx={v:i for i,v in enumerate(free)}
    bonds={(v,w):0 for v in free for w in NEIGH[v] if w in idx and v<w}
    bonds={k:i+n for i,k in enumerate(bonds)}
    assert len(bonds)+n==N
    # All five subcubes orientations containing the first four axes.
    for outer in range(4,9):
        axes=15|(1<<outer)
        for base in range(512):
            if base&axes:continue
            T={v for v in range(512) if v&~axes==base}
            ids=[idx[v] for v in sorted(T) if v in idx]
            ff=[bonds[v,w] for v in sorted(T) if v in idx for w in NEIGH[v]
                if w in T and w in idx and v<w]
            inc=[len(adj[v]&T) for v in sorted(T) if v in idx]
            M=T&R;me=sum(len(adj[v]&T) for v in M)//2
            rows.append((ids+ff,[14*k-13 for k in inc]+[14]*len(ff),13*len(M)-14*me))
            if M:
                rows.append((ids+ff,[k-1 for k in inc]+[1]*len(ff),len(M)-1-me))
    return nr,n,N,rows

if __name__=="__main__":
    print("Q5 normalized oriented 14-vertex paths",check_q5(),flush=True)
    cases=list(layouts())
    import sys
    jobs=[(str(i),cases[i]) for i in map(int,sys.argv[1:])]
    jobs.append(("cycle",check()))
    with gzip.open(ROOT/"q9_port_fiveface_trials.jsonl.gz","wt") as f:
        for k,es in jobs:
            b,d,w=solve(es,builder=build5)
            print(k,b,flush=True)
            f.write(json.dumps(dict(case=k,edges=es,upper=b,den=d,weights=w))+"\n")
