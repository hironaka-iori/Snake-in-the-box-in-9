"""Keep one full 98-edge Q8 record except holes; let the opposite slice vary freely."""
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import json,sys,os
from search_q9_shell_dual import solve
from verify_q9_center_avoidance import verify
def run(job):
    holes,ep,g,arm=job
    fixed={v for j,v in enumerate(arm) if j not in holes}
    assert fixed
    deg={v:sum(v^1<<d in fixed for d in range(8)) for v in fixed}
    # A fixed lower vertex of degree two forbids its counterpart in the upper slice.
    domain=fixed|{v+256 for v in range(256) if deg.get(v,0)<2}
    unrestricted=os.environ.get("Q9_FREE_BOTTOM")=="1"
    if unrestricted:
        for v in set(range(256))-fixed:
            adjacent={v^1<<d for d in range(8)} & fixed
            if len(adjacent)<=2 and all(deg[x]<2 for x in adjacent):domain.add(v)
    i,r,ep,g,st,u,w=solve((0,arm,0,ep,g,320000,fixed,domain))
    if w:
        verify(w);bottom={v for v in w if v<256}
        assert (fixed<=bottom if unrestricted else fixed==bottom)
    return [holes,ep,g,st,u,w]
if __name__=="__main__":
    arm=json.loads(open("q8_free_layer_full98_duals.jsonl").readline())["certificate"]["arm"];verify(arm);assert len(arm)==99
    ctrl=run(((),(arm[0]+256).bit_count()%2,100,arm));assert ctrl[3]=="FOUND";print(json.dumps(ctrl),flush=True)
    h=int(sys.argv[1]);holes=list(combinations(range(99),h))
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(run,[(idx,e,192,arm) for idx in holes for e in (0,1)],chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
