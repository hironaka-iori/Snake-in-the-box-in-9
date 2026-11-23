"""Independent cardinality-SAT formulation with connectivity cuts and a free Q9."""
import json
from concurrent.futures import ProcessPoolExecutor
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import verify
def check(job):
    i,p,g=job;fixed=set(p);fixed.discard(p[i])
    st,w=search(fixed,set(p),g,80000,at_least=True)
    if w:verify(w);assert fixed<=set(w) and len(w)>g
    return i,g,st,w
if __name__=="__main__":
    p=json.loads(open("q8_free_layer_full98_duals.jsonl").readline())["certificate"]["arm"];verify(p)
    with ProcessPoolExecutor(2) as pool:
        for r in pool.map(check,[(0,p,98)]+[(i,p,192) for i in range(99)],chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[1]>=192 and r[-1]:break
