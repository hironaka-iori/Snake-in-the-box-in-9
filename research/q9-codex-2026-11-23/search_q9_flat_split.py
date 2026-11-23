"""Partition each unresolved affine-flat search by fixed vertex decisions."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import json,sys
from search_q9_free_record_slice import parents,search,verify
from search_q9_anchored_sets import NB
def init():
    global bank
    bank=parents()
def split(i,b):
    patch={v for v in range(512) if all((v&(m&511)).bit_count()%2==m>>9 for m in b)}
    p=set(bank[i]);fixed=p-patch
    degree=[len(fixed.intersection(n)) for n in NB]
    sat={v for v in fixed if degree[v]==2}
    pool={v for v in patch if degree[v]<=2 and sat.isdisjoint(NB[v])}
    piv=[]
    while len(piv)<7 and pool-set(piv):
        v=max(pool-set(piv),key=lambda v:(degree[v]+min(2,len(pool.intersection(NB[v]))/4), min(((v^u).bit_count() for u in piv),default=10),v in p,v))
        piv.append(v)
    return fixed,patch,piv
def work(args):
    i,b,c,cap=args
    fixed,patch,piv=split(i,b)
    on={v for j,v in enumerate(piv) if (c>>j)&1}
    off=set(piv)-on
    st,w=search(fixed|on,set(bank[i]),192,cap,allowed=(fixed|patch)-off,at_least=True)
    if w:
        verify(w);assert len(w)>=193 and (set(w)^set(bank[i]))<=patch and on<=set(w) and not off.intersection(w)
    return i,b,c,st,w
if __name__=="__main__":
    init()
    parents_left=[(i,b) for i,b,o,_ in map(json.loads,open("q9_codim2_allcuts_retry.jsonl")) if o=="UNKNOWN"]
    jobs=((i,b,c,20000) for i,b in parents_left for c in range(1<<len(split(i,b)[2])))
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for r in pool.map(work,jobs,chunksize=3,buffersize=48):
            print(json.dumps(r),flush=True)
            if r[-1]:break
