"""Bound a Q9 snake containing prescribed crossing edges; extra crossings are allowed."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import gzip
import sys
from bound_q9_paired_faces import bits, offsets, catalog

# Integer bitsets index all locally valid induced Q4 forests, largest first.
def build_tables():
    forests=[]
    for mask in range(1<<16):
        if mask.bit_count()>8:
            continue
        todo=mask
        degs={i:sum((mask>>(i^(1<<j)))&1 for j in range(4)) for i in bits(mask)}
        if max(degs.values(),default=0)>2:
            continue
        while todo:
            stack=[(todo & -todo).bit_length()-1]
            component=0
            while stack:
                v=stack.pop()
                if component>>v&1:continue
                component |= 1<<v
                stack.extend(w for j in range(4) if mask>>(w:=v^(1<<j))&1 and not component>>w&1)
            if all(degs[v]==2 for v in bits(component)):break
            todo &= ~component
        if not todo:forests.append((mask,degs))
    assert len(forests)==sum(map(len,catalog))
    forests.sort(key=lambda entry:-entry[0].bit_count())
    sizes=[m.bit_count() for m,_ in forests]
    n=len(sizes)
    tables=[[bytearray((n+7)//8) for _ in range(16)] for _ in range(3)]
    for i,(mask,degs) in enumerate(forests):
        for v,d in degs.items():
            for j in range(d+1):tables[j][v][i//8]|=1<<(i%8)
    return sizes,[[int.from_bytes(a,"little") for a in row] for row in tables]
sizes,tables=build_tables()

def bound(required, *, return_faces=False, fixed_faces=None):
    adj=[sum(1<<i for i in range(9) if (v^(1<<i)) in required) for v in range(512)]
    saturated={v for v in required if adj[v].bit_count()==2}
    banned={v for v in range(512) if v not in required and (adj[v].bit_count()>2 or any((v^(1<<i)) in saturated for i in range(9)))}
    @lru_cache(None)
    def visit(base,free):
        if free.bit_count()==4:
            allowed=(1<<len(sizes))-1
            for i,z in enumerate(offsets(free)):
                v=base|z
                if v in required:allowed &= tables[0][i]
                if v in banned:allowed &= ~tables[0][i]
                else:
                    outside=(adj[v] & ~free).bit_count()
                    if outside:allowed &= ~tables[max(0,3-outside)][i]
            if not allowed:raise ValueError("Incompatible prescribed vertices")
            return sizes[(allowed & -allowed).bit_length()-1]
        return min(visit(base,free^(1<<i))+visit(base|(1<<i),free^(1<<i)) for i in bits(free))
    if fixed_faces is not None:
        return sum(visit(b,f) for b,f in fixed_faces)-1
    value=visit(0,511)-1
    if not return_faces:return value
    def recover(b,f):
        if f.bit_count()==4:return [(b,f)]
        for i in bits(f):
            t=1<<i
            if visit(b,f)==visit(b,f^t)+visit(b|t,f^t):
                return recover(b,f^t)+recover(b|t,f^t)
        raise AssertionError
    return value,recover(0,511)

def crossing_edges(path,d):
    return [(a,b) for a,b in zip(path,path[1:]) if a^b==1<<d]

if __name__=="__main__":
    with gzip.open(Path(__file__).with_name("q9_port_followup_public191.txt.gz"),"rt") as f:
        bank=[list(map(int,s.split())) for s in f]
    for r in map(int,sys.argv[1:] or [0]):
        p=bank[r]
        assert len(set(p))==len(p)==192 and all(0<=x<512 for x in p)
        assert all(((v^u).bit_count()==1)==(j+1==i) for i,v in enumerate(p) for j,u in enumerate(p[:i]))
        ds=sorted(range(9),key=lambda d:(-len(crossing_edges(p,d)),d))
        for axes in (ds[:1],ds[:2]):
            es=[e for d in axes for e in crossing_edges(p,d)]
            S=set(v for e in es for v in e)
            b=bound(S);assert b>=191
            print(r,axes,len(es),len(S),b,flush=True)
