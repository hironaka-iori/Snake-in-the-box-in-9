"""Grow independently verified 189-edge seeds while retaining eligibility for 192."""
from concurrent.futures import ProcessPoolExecutor
from collections import Counter
import gzip,json,random
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import forms,verify

def init():
    global bank,parents
    parents=[r["vertices"] for r in json.load(open("q9_center_avoidance_verified.json"))["new_witnesses"]]
    bank=set()
    for file in ["q9_free_bridge_join_inputs.txt.gz","q9_centers_1042_inputs.txt.gz"]:
        for line in gzip.open(file,"rt"):bank.update(forms(list(map(int,line.split())),142))
    assert len(bank)==17974 and len(parents)==18
    for p in parents:
        verify(p);assert not bank.intersection(forms(p,142))

def excluded(p):
    for i,x in enumerate(forms(p,142)):
        if x in bank:return p[i:i+143]

def work(job):
    i,m,s=job;p=parents[i]
    side={v for v in p if (v&m).bit_count()%2==s}
    free={v for v in range(512) if (v&m).bit_count()%2!=s}
    st,w=search(side,set(p),190,6000,allowed=side|free,reject_fragment=excluded,at_least=True)
    if w:
        verify(w);assert len(w)>=191 and not excluded(w) and set(w)-free==side
    return [i,m,s,st,w]

if __name__=="__main__":
    init()
    jobs=[(i,m,s) for i in range(len(parents)) for m in range(1,512) for s in (0,1)]
    random.Random(194011).shuffle(jobs)
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for r in pool.map(work,jobs,chunksize=4,buffersize=32):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1] and len(r[-1])>=193:break
