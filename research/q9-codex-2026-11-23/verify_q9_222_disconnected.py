"""Verify an integral 222-vertex obstruction to local four-face bounds."""
import json
from itertools import combinations
from q9_overlapping_port_bound import ROOT,NEIGH,FACES
from q9_port_pattern_match import patterns,contained
def components(S):
    todo=set(S);out=[]
    while todo:
        v=todo.pop();part={v};stack=[v]
        while stack:
            w=stack.pop()
            for n in NEIGH[w]:
                if n in todo:
                    todo.remove(n);part.add(n);stack.append(n)
        out.append(part)
    return out
def check():
    A={0,1,3,4,7,13,15,20,22,24,25,26,29,30}
    B={2,6,8,9,11,12,14,16,17,18,21,23,27,31}
    assert A.isdisjoint(B)
    S={32*y+x for y in range(16) for x in (B if y.bit_count()%2 else A)}-{0,1}
    edges=sorted((v,w) for v in S for w in NEIGH[v] if v<w and w in S)
    parts=components(S)
    assert len(S)==222 and len(edges)==221
    assert sorted(map(len,parts))==[12]+[14]*15
    degrees=[sum(w in S for w in NEIGH[v]) for v in S]
    assert sorted(degrees)==[1]*2+[2]*220
    for _,_,face in FACES:
        T=set(face)&S
        for comp in components(T):
            assert any(sum(w in comp for w in NEIGH[v])<2 for v in comp)
    directions=sorted(range(9),key=lambda d:-sum(a^b==1<<d for a,b in edges))
    es=sum(([(a,b) for a,b in edges if a^b==1<<d][:25] for d in directions[:2]),[])
    assert len(es)==50
    req={v for e in es for v in e}
    ps=patterns()
    assert all(not contained(p,req) for p in ps)
    print("directions",[sum((a^b)==1<<d for a,b in edges) for d in range(9)])
    print("full old-pattern containment",[contained(p,S) for p in ps])
    print("Q4 faces",len(FACES),"vertices",len(S),"edges",len(edges),"cycles",len(parts)-1)
    return es

if __name__=="__main__":check()
