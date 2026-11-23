"""Explore neutral and length-increasing exchanges with exact induced-path checks."""
import json,os,subprocess
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from verify_q9_center_avoidance import verify,forms
from pathlib import Path
blocked={bytes(map(int,x)) for x in Path("q9_excluded_142_lex.txt").read_text().split()}
def visit(job):
    key,p,g,seed,rounds=job
    raw=subprocess.check_output(["/tmp/q9_contact_exchange_neutral20","9",str(rounds),str(seed),str(g)],env=dict(os.environ,Q9_AVOID_SHAPES="q9_excluded_142_lex.txt"),input=" ".join(map(str,p))+"\n",text=True).split()
    if raw[1]=="SAMPLED":return key,g,seed,None,None
    assert raw[1]=="FOUND"
    w=list(map(int,raw[5:]));verify(w);assert len(w)==len(p)+g and max(w)<512
    assert blocked.isdisjoint(forms(w,142))
    return key,g,seed,forms(w,len(w)-1)[0],w
if __name__=="__main__":
    q=deque();seen=set()
    for r in json.load(open("q9_center_avoidance_verified.json"))["new_witnesses"]:
        p=r["vertices"];key=forms(p,len(p)-1)[0]
        if key not in seen:q.append((key,p));seen.add(key)
    tested=0
    with ThreadPoolExecutor(3) as pool:
        while q and tested<400:
            k,p=q.popleft();jobs=[(k,p,g,193192+tested*101+j+(20 if g else 0),80 if g else 12) for g in (1,0) for j in range(3 if g else 12)]
            hits=[]
            for _,g,seed,nk,w in pool.map(visit,jobs):
                if nk is None or nk in seen:continue
                seen.add(nk);(q.appendleft if g else q.append)((nk,w))
                hits.append([g,seed,w]);print(json.dumps({"parent":k.hex(),"gain":g,"seed":seed,"edges":len(w)-1,"vertices":w},separators=(",",":")),flush=True)
                if len(w)>=193:raise SystemExit(0)
            tested+=1
            print(json.dumps({"visited":tested,"frontier":len(q),"distinct":len(seen),"gains":[j[0] for j in hits]}),flush=True)
