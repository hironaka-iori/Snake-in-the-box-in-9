"""Hold a new Q8 arm as the complete lower layer, permit every upper-layer vertex."""
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import verify,forms
import json
def run(job):
    key,p,goal,budget=job
    fixed=set(p)
    st,w=search(fixed,fixed,goal,budget,allowed=fixed|set(range(256,512)),at_least=True)
    if w:
        verify(w);assert len(w)>goal and {x for x in w if x<256}==fixed
    return key,goal,st,w
if __name__=="__main__":
    unique={}
    for word in Path("q8_exchange_new_rooted_arms.txt").read_text().split():
        p=[0]
        for c in word:p.append(p[-1]^(1<<int(c)))
        verify(p);unique.setdefault(forms(p,len(p)-1)[0],p)
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(run,((key.hex(),p,g,150000) for key,p in unique.items() for g in (192,195,196)),chunksize=1):
            print(json.dumps(r),flush=True)
            if r[-1]:break
