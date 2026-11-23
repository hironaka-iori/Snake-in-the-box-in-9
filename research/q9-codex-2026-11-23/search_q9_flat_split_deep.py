"""Subdivide only the still unresolved seven-decision leaves."""
import json
from concurrent.futures import ProcessPoolExecutor
import search_q9_flat_split as first
from search_q9_anchored_sets import NB,search

def prep(i,b,c):
    fixed,patch,piv=first.split(i,b)
    fixed|={v for j,v in enumerate(piv) if c>>j&1}
    domain=(fixed|patch)-{v for j,v in enumerate(piv) if not c>>j&1}
    degree=[len(fixed.intersection(n)) for n in NB]
    sat={v for v in fixed if degree[v]==2}
    pool={v for v in domain-fixed if degree[v]<=2 and sat.isdisjoint(NB[v])}
    chosen=[]
    while len(chosen)<7 and pool:
        v=max(pool,key=lambda v:(min(((v^u).bit_count() for u in chosen),default=0),
              len(pool.intersection(NB[v]))+degree[v],v in first.bank[i],v))
        chosen.append(v);pool.remove(v)
    return fixed,domain,chosen

def work(args):
    i,b,c,d=args;fixed,domain,chosen=prep(i,b,c)
    fix=fixed|{v for j,v in enumerate(chosen) if d>>j&1}
    allowed=domain-{v for j,v in enumerate(chosen) if not d>>j&1}
    st,w=search(fix,set(first.bank[i]),192,100000,allowed=allowed,at_least=True)
    if w:first.verify(w);assert len(w)>=193 and fix<=set(w)<=allowed
    return i,b,c,d,st,w

if __name__=="__main__":
    first.init()
    todo=[(i,b,c) for i,b,c,st,w in map(json.loads,open("q9_codim2_splits.jsonl")) if st=="UNKNOWN"]
    jobs=((i,b,c,d) for i,b,c in todo for d in range(1<<len(prep(i,b,c)[2])))
    with ProcessPoolExecutor(4,initializer=first.init) as pool:
        for r in pool.map(work,jobs,chunksize=4,buffersize=40):
            print(json.dumps(r),flush=True)
            if r[-1]:break
