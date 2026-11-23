"""Independent native cardinality model on the original point labels.

No degree propagation, edge-count prefix DFS or coordinate inverse construction
is shared with the C++ search. Models are accepted only after graph validation.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
from random import Random
import json,sys
from pysat.solvers import Minicard
D=Path(__file__).resolve().parent; R=D.parent
def path(w):
    p=[0]
    for d in w:p.append(p[-1]^1<<int(d))
    return p
def rank(bs):
    span={0}
    for g in bs:span|={x^g for x in span}
    return len(span)==512
def trace(s,bs):
    adj={x:[x^g for g in bs if x^g in s] for x in s}
    if any(len(ns)>2 for ns in adj.values()):return None
    tips=[x for x,ns in adj.items() if len(ns)==1]
    if len(tips)!=2:return None
    out=[];prev=None;x=tips[0]
    while x is not None:
        out.append(x);x,prev=next((y for y in adj[x] if y!=prev),None),x
    if len(out)!=len(s):return None
    return out
def complete(s,bs,holes):
    # Independent physical oracle tries every unordered set of optional points
    # once. Restrict to points touching at most two original vertices, all with
    # room for one new edge. For h=1,2 and n>0 every valid extra point is at
    # distance at most h from the original set.
    if not holes:return trace(s,bs)
    deg={x:sum(x^g in s for g in bs) for x in s}
    candidates=[]
    for v in set(range(512))-s:
        nei=[v^g for g in bs if v^g in s]
        if len(nei)>2 or any(deg[x]>=2 for x in nei):continue
        candidates.append((v,len(nei)))
    req=len(s)+holes-1-sum(deg.values())//2
    for chosen in combinations(candidates,holes):
        vs=[v for v,_ in chosen];bonds=sum((x^y) in bs for x,y in combinations(vs,2))
        if sum(n for _,n in chosen)+bonds!=req:continue
        p=trace(s|set(vs),bs)
        if p:return p
def solve(p,holes,mask,cap,preferred=None):
    # Each mandatory point must eventually have two incidences, except for
    # global endpoints. Deleting h optional vertices leaves at most h+1
    # components, i.e. total degree deficit between 2 and 2h+2.
    s=set(p);assert len(s)==len(p)
    active=[g for g in range(1,512) if (g&mask).bit_count()%2];base=511
    colors=sum((v&mask).bit_count()%2 for v in p)
    if max(colors,len(s)-colors)>(len(s)+holes+1)//2:return dict(status='PARITY')
    attempts=0
    with Minicard() as sat:
        def at_least(xs,b):sat.add_atmost([-x for x in xs],len(xs)-b)
        sat.add_atmost(active,9);at_least(active,9);tokens=[]
        for v in p:
            inc=[g for g in active if v^g in s]
            ds=list(range(base+1,base+2+(holes>0)));base=ds[-1];tokens.extend(ds)
            if len(ds)==2:sat.add_clause([-ds[1],ds[0]])
            sat.add_atmost(inc+ds,2);at_least(inc+ds,2)
        sat.add_atmost(tokens,2*(holes+1));at_least(tokens,2)
        if preferred:sat.set_phases([a if a in preferred else -a for a in active])
        while True:
            remaining=cap-sat.accum_stats()['conflicts']
            if remaining<=0:return dict(status='LIMIT',models=attempts)
            sat.conf_budget(remaining);z=sat.solve_limited()
            if z is not True:return dict(status='CLOSED' if z is False else 'LIMIT',models=attempts,conflicts=sat.accum_stats()['conflicts'])
            picked={g for g in active if g in set(sat.get_model())};assert len(picked)==9;attempts+=1
            if rank(picked):
                w=complete(s,picked,holes)
                if w:
                    assert s<=set(w) and len(w)==len(s)+holes
                    assert all(((x^y) in picked)==(i+1==j) for j,y in enumerate(w) for i,x in enumerate(w[:j]))
                    return dict(status='FOUND',models=attempts,conflicts=sat.accum_stats()['conflicts'],basis=sorted(picked),ordered_original_points=w)
            sat.add_clause([-g for g in picked])
def main():
    words=(R/'q9_change_basis/windows192.txt').read_text().split();bank=(R/'q9_gap_generations/prior191.words').read_text().split()
    tests=[('window',row,0,mask,path(words[row]),None) for row,mask in ((0,511),(2,511),(6,9),(31,511),(200,511))]+[('plus_one',row,1,511,path(bank[row]),set(1<<j for j in range(9))) for row in (0,2,31,98)]
    rng=Random(82801)
    for h in (0,1,2):
        for r in (1,19):
            w=path(bank[r]);bs=[1<<j for j in range(9)];rng.shuffle(bs)
            for t in range(31):
                a,b=rng.sample(range(9),2);bs[a]^=bs[b]
            mask=next(m for m in range(1,512) if all((m&g).bit_count()%2==1 for g in bs))
            p=[0]
            for c in bank[r]:p.append(p[-1]^bs[int(c)])
            gone=rng.sample(range(4,187),h);p=[v for j,v in enumerate(p) if j not in gone];rng.shuffle(p)
            tests.append(('gl_control',r,h,mask,p,set(bs)))
    for name,r,h,m,p,ph in tests:
        result=solve(p,h,m,40000,ph)
        print(json.dumps(dict(test=name,row=r,holes=h,mask=m,**result)),flush=True)
if __name__=='__main__':main()
