"""Revisit only unresolved endpoint colors, using more face partitions."""
import json,sys
from concurrent.futures import ProcessPoolExecutor
from search_q9_shell_dual import parents,solve
if __name__=="__main__":
    records=list(map(json.loads,open("q9_shell3_duals_192.jsonl")))
    assert len(records)==265
    left=[(i,r,e) for i,r,e,g,st,_,_ in records if g==192 and st=="UNKNOWN"]
    bank=parents()
    with ProcessPoolExecutor(2) as pool:
        for r in pool.map(solve,[(i,bank[i],r,e,192,2000000) for i,r,e in left]):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
