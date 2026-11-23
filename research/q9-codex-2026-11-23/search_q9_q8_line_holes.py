"""Cover all pairs of omitted vertices of the Q8 witness by affine lines over F_11."""
from search_q9_punctured_q8 import run
from verify_q9_center_avoidance import verify
import json,itertools,random,os
from concurrent.futures import ProcessPoolExecutor
def blocks():
    ids=list(range(99));random.Random(80692).shuffle(ids)
    groups=[]
    for orientation in range(12):
        for b in range(11):
            group=tuple(sorted(ids[j] for j in range(99) if (j%11==b if orientation==11 else (j//11-orientation*(j%11))%11==b)))
            if len(group)>=2:groups.append(group)
    pairs=[x for group in groups for x in itertools.combinations(group,2)]
    assert len(pairs)==len(set(pairs))==99*98//2
    return groups
if __name__=="__main__":
    assert os.getenv("Q9_FREE_BOTTOM")=="1"
    arm=json.loads(open("q8_free_layer_full98_duals.jsonl").readline())["certificate"]["arm"];verify(arm)
    with ProcessPoolExecutor(3) as pool:
        for r in pool.map(run,[(holes,e,192,arm) for holes in blocks() for e in (0,1)],chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
