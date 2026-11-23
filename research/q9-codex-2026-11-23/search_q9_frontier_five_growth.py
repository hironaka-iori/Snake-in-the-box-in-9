"""Prioritize promising, nonisometric 189-edge donors for larger exact exchanges."""
from concurrent.futures import ProcessPoolExecutor
from collections import deque
from pathlib import Path
import json,os,subprocess
from verify_q9_center_avoidance import verify,forms
from search_q9_new_frontier_growth import run
def score(p):
    used=set(p);ends={p[0],p[-1]}
    low=0;offset=0
    for x in range(512):
        if x in used:continue
        nb=[x^(1<<j) for j in range(9) if (x^(1<<j)) in used]
        if len(nb)<=3:low+=4-len(nb);offset+=len(ends.intersection(nb))
    return low,offset
def try_parent(job):
    p,k=job;row=run(p,k)
    if row[-1]:
        blocked={bytes(map(int,w)) for w in Path("q9_excluded_142_lex.txt").read_text().split()}
        assert blocked.isdisjoint(forms(row[-1],142));verify(row[-1])
    return row
if __name__=="__main__":
    rows=[r["vertices"] for r in map(json.loads,open("q9_neutral_eligible_growth.jsonl")) if r.get("edges")==189]
    seedbank={forms(p,len(p)-1)[0]:p for p in rows};assert len(seedbank)==len(rows)
    staged=sorted(rows,key=score,reverse=True)
    with ProcessPoolExecutor(2) as pool:
        for r in pool.map(try_parent,((p,5) for p in staged),chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:
                q=deque([r[-1]])
                while q:
                    p=q.popleft()
                    if len(p)>=193:raise SystemExit
                    for k in range(1,6):
                        nxt=try_parent((p,k));print(json.dumps(nxt,separators=(",",":")),flush=True)
                        if nxt[-1]:q.append(nxt[-1])
