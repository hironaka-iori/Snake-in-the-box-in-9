"""Complete or record the unresolved leaves of one anchored search by binary splits."""
from collections import deque
from pathlib import Path
import json
import sys
from search_q9_anchored_sets import NB
from search_q9_junction_last_cases import Balanced,anchored,check,sources

def choose(fixed,excluded,guide):
    degrees=[len(fixed.intersection(nb)) for nb in NB]
    saturated={v for v in fixed if degrees[v]==2}
    avail={v for v in range(512) if v not in fixed|excluded and degrees[v]<=2
           and not saturated.intersection(NB[v])}
    # Prefer a branching vertex touching a required chain and multiple usable neighbors.
    return max(avail,key=lambda v:(degrees[v]==1,len(avail.intersection(NB[v])),v in guide,-v))

def main():
    _,_,p,_=next(sources(Path(sys.argv[1])))
    roots=[json.loads(s) for s in Path(sys.argv[2]).read_text().splitlines()]
    queue=deque((set(r["fixed"]),set(r["excluded"])) for r in roots if r["status"]=="UNKNOWN")
    allowed=set(range(512))
    for _ in range(int(sys.argv[3])):
        if not queue:break
        fixed,excluded=queue.popleft()
        anchored.Minicard=lambda:Balanced(0,fixed,192)
        status,w=anchored.search(fixed,set(p),192,int(sys.argv[4]),allowed=allowed-excluded)
        split=None
        if w:
            check(w,192)
            assert len(w)==193 and fixed<=set(w)<=allowed-excluded
        elif status=="UNKNOWN":
            split=choose(fixed,excluded,set(p))
            queue.append((fixed|{split},excluded))
            queue.append((fixed,excluded|{split}))
        print(json.dumps(dict(fixed=sorted(fixed),excluded=sorted(excluded),
                              split=split,status=status,witness=w,pending=len(queue))),flush=True)
        if w:return
if __name__=="__main__":main()
