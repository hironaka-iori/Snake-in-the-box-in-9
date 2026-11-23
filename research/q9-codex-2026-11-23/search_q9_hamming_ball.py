"""Freely replace the contents of a Hamming ball around any Q9 center."""
import json,random
from concurrent.futures import ProcessPoolExecutor
from search_q9_free_record_slice import parents,verify,search

def init():
    global bank,ball
    bank=parents()
    ball=[frozenset(v for v in range(512) if (v^c).bit_count()<=4) for c in range(512)]
    assert all(len(b)==256 and not b.intersection(ball[c^511]) for c,b in enumerate(ball))

def solve(job):
    i,c,t,cap=job
    record=bank[i];fixed=set(record)-ball[c]
    st,w=search(fixed,set(record),t,cap,allowed=fixed|ball[c],at_least=True)
    if w:
        verify(w);assert len(w)>t and set(w)-ball[c]==fixed
    return i,c,t,st,w

if __name__=="__main__":
    jobs=[(i,c,192,4000) for i in range(131) for c in range(512)]
    random.Random(934).shuffle(jobs)
    controls=[(i,c,191,4000) for i,c,_,_ in jobs[:30]]
    with ProcessPoolExecutor(4,initializer=init) as p:
        for r in p.map(solve,controls+jobs,chunksize=6,buffersize=64):
            print(json.dumps(r),flush=True)
            if r[-1] and len(r[-1])>=193:break
