"""Integer-replayable upper bounds for 221-edge Q9 snakes containing specified edges."""
import gzip
import json
import random
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from bound_q9_positive_ports import offsets, crossing_edges, sizes, tables

ROOT=Path(__file__).resolve().parent
NEIGH=[tuple(v^(1<<d) for d in range(9)) for v in range(512)]
FACES=[(base,mask,tuple(base|x for x in offsets(mask)))
       for mask in range(512) if mask.bit_count()==4 for base in range(512) if base&mask==0]

def controls():
    rng=random.Random(221)
    with gzip.open(ROOT/"q9_port_followup_public191.txt.gz","rt") as stream:
        for s in stream:
            p=list(map(int,s.split()))
            pools=sorted((crossing_edges(p,d) for d in range(9)),key=lambda a:-len(a))
            yield rng.sample(pools[0],25)+rng.sample(pools[1],25)

@lru_cache(maxsize=100000)
def face_cap(must,ban,one,two):
    allowed=(1<<len(sizes))-1
    for mask,tab,neg in [(must,0,False),(ban,0,True),(one,2,True),(two,1,True)]:
        while mask:
            bit=mask&-mask; col=tables[tab][bit.bit_length()-1]
            allowed &= (~col if neg else col)
            mask-=bit
    if not allowed:raise ValueError("infeasible local face")
    return sizes[(allowed&-allowed).bit_length()-1]

def constraints(edges):
    req={v for e in edges for v in e}
    occ=[sum(1<<d for d,w in enumerate(NEIGH[v]) if w in req) for v in range(512)]
    sat={v for v in req if occ[v].bit_count()==2}
    ban={v for v in range(512) if v not in req and (occ[v].bit_count()>2 or sat.intersection(NEIGH[v]))}
    free=sorted(set(range(512))-req-ban)
    idx={v:i for i,v in enumerate(free)}
    rows=[]
    for _,mask,face in FACES:
        m=b=o=t=0
        for i,v in enumerate(face):
            if v in req:m|=1<<i
            if v in ban:b|=1<<i
            ext=(occ[v]&~mask).bit_count()
            if ext>=1:o|=1<<i
            if ext>=2:t|=1<<i
        ids=[idx[v] for v in face if v in idx]
        cap=face_cap(m,b,o,t)-m.bit_count()
        if cap<len(ids):rows.append((ids,[1]*len(ids),cap))
    for v in sorted(req|set(free)):
        ids=[idx[w] for w in NEIGH[v] if w in idx]
        residual=2-occ[v].bit_count()
        if len(ids)<=residual:continue
        if v in req:rows.append((ids,[1]*len(ids),residual))
        else:rows.append((ids+[idx[v]],[1]*len(ids)+[len(ids)-residual],len(ids)))
    return len(req),len(free),rows

def replay(edges,weights,den):
    nr,n,rows=constraints(edges)
    coeff=[0]*n
    cost=nr*den
    for j,a in weights:
        assert isinstance(a,int) and a>=0 and 0<=j<len(rows)
        ids,vals,rhs=rows[j];cost+=a*rhs
        for k,b in zip(ids,vals):coeff[k]+=a*b
    cost+=sum(max(0,den-c) for c in coeff)
    return cost//den-1

def solve(edges):
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    nr,n,rows=constraints(edges)
    ix=[]; vals=[]; starts=[0]
    for ids,vs,_ in rows:
        ix.extend(ids); vals.extend(vs); starts.append(len(ix))
    A=csr_matrix((vals,ix,starts),shape=(len(rows),n))
    lp=linprog([-1]*n,A_ub=A,b_ub=[r[2] for r in rows],bounds=(0,1),method="highs")
    assert lp.success
    den=100000
    w=[(i,round(-v*den)) for i,v in enumerate(lp.ineqlin.marginals) if round(-v*den)>0]
    return replay(edges,w,den),den,w

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument("--out",required=True);ap.add_argument("rows",nargs="*",type=int)
    args=ap.parse_args()
    old=[int(s.split()[1]) for s in (ROOT/"q9_positive_ports_balanced50_20261121.txt").read_text().splitlines()]
    layouts=list(controls())
    with gzip.open(args.out,"wt") as f:
        for i in args.rows or range(len(layouts)):
            edges=layouts[i];bound,den,w=solve(edges)
            assert bound>=191
            f.write(json.dumps(dict(row=i,edges=edges,old=old[i],upper=bound,den=den,weights=w))+"\n")
            print(i,old[i],bound,flush=True)
