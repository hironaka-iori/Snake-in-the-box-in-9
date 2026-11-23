"""Dimension-split bounds and independent checks of the finite witnesses."""
import itertools
import gzip
import json
from pathlib import Path
from functools import lru_cache
HERE=Path(__file__).resolve().parent

def parts(S,d):
    remaining=set(S);out=[]
    while remaining:
        x=remaining.pop();C={x};stack=[x]
        while stack:
            v=stack.pop()
            for j in range(d):
                w=v^(1<<j)
                if w in remaining:remaining.remove(w);C.add(w);stack.append(w)
        out.append(C)
    return out

def deg(S,v,d):
    return sum((v^(1<<j)) in S for j in range(d))
def maskset(m):return {i for i in range(64) if m>>i&1}

# Source: arXiv:2607.15270v3, Table 3 and Appendix D. A Q7 forest has at most 64 vertices.
def edge7(c):
    if c<0 or c>64:return -1000
    return (0,50,50,50,52,51,50,49,48)[c] if c<=8 else min(48,64-c)

def q8_two_upper():
    possible=[]
    for e in range(127):
        for t in range(e//8+1):
            if any(e-t<=edge7(a)+edge7(2+t-a) for a in range((t+1)//2,2+t-(t+1)//2+1)):
                possible.append(e);break
    return max(possible)

def two_axis_caps():
    states={(0,(1,0,0,0))};bounds=[]
    for k in range(16):
        bounds.append(k+max(sum(map(edge7,c)) for u,c in states))
        nxt=set()
        for u,c in states:
            for v in (u^1,u^2):
                cs=list(c);cs[v]+=1;nxt.add((v,tuple(cs)))
        states=nxt
    return bounds

def verify():
    bounds=two_axis_caps();upper=q8_two_upper()
    assert upper==110 and max(bounds[:15])==220
    words=(HERE/"q9_208_tile.log").read_text().split()
    A,B=[maskset(int(w,16)) for w in words[1:]]
    assert not A&B
    for C in [A,B]:
        assert len(C)==26 and len(parts(C,6))==1 and all(deg(C,v,6)==2 for v in C)
        assert all(len({v>>d&1 for v in C})==2 for d in range(6))
    S={64*z+v for z in range(8) for v in (B if z.bit_count()%2 else A)}
    ps=parts(S,9)
    assert len(S)==208 and len(ps)==8 and all(len(p)==26 for p in ps)
    assert all(deg(S,v,9)==2 for v in S)
    # A Q5 restriction can only have a cycle if it contains a whole ambient cycle.
    for D in itertools.combinations(range(9),5):
        mask=sum(1<<d for d in D)
        assert all(len({v&~mask for v in C})>1 for C in ps)
    for l in (HERE/"q9_sixdim_density.log").read_text().splitlines():
        if l.startswith("Q6 vertices"):
            row=l.split();n,k=int(row[2]),int(row[4]);P=maskset(int(row[-1],16));cs=parts(P,6)
            assert len(P)==n and len(cs)==k and all(deg(P,v,6)<=2 for v in P)
            assert all(any(deg(C,v,6)<2 for v in C) for C in cs)
    bankrows=0
    with gzip.open(HERE/"q9_port_followup_public191.txt.gz","rt") as f:
        for l in f:
            p=list(map(int,l.split()));assert len(set(p))==len(p)==192
            assert all(((v^w).bit_count()==1)==(i-j==1) for i,v in enumerate(p) for j,w in enumerate(p[:i]))
            for d,e in itertools.combinations(range(9),2):
                v=[0]*4;last=-1
                for x in p:
                    cell=(x>>d&1)+2*(x>>e&1)
                    if cell!=last:v[cell]+=1;last=cell
                k=sum(v)-1
                assert len(p)-1<=k+sum(map(edge7,v))
            bankrows+=1
    return dict(two_axis_caps_k0_to_15=bounds,
                Q8_two_component_edge_upper=upper,Q9_at_most_two_crossings_upper=98+2+upper,
                control_projection_checks=bankrows*36,verified_tile_vertices=len(S))
if __name__=="__main__":print(json.dumps(verify(),indent=1))
