"""Use the middle Q8 segments of actual two-crossing Q9 paths to seed new lifts."""
import gzip,json,subprocess
from concurrent.futures import ProcessPoolExecutor
from collections import Counter
from pathlib import Path
from grow_q8_exchange_bank import norm
from verify_q9_center_avoidance import forms,verify

def collect():
    bank={}
    for f in ("q9_free_bridge_join_inputs.txt.gz","q9_centers_1042_inputs.txt.gz"):
        for line in gzip.open(f,"rt"):
            p=list(map(int,line.split()))
            for axis in range(9):
                crossings=[j for j,(v,w) in enumerate(zip(p,p[1:])) if v^w==1<<axis]
                if len(crossings)!=2:continue
                a,b=crossings
                old=p[a+1:b+1];base=old[0]
                def image(v):
                    x=v^base
                    return (x&((1<<axis)-1))|((x>>(axis+1))<<axis)|(((x>>axis)&1)<<8)
                full=[image(v) for v in p]
                arm=full[a+1:b+1];key=forms(arm,len(arm)-1)[0]
                verify(full);verify(arm)
                if key not in bank or len(full)>len(bank[key][1]):bank[key]=arm,full
    return list(bank.values())

def mut(job):
    p,full,k,g=job
    U={v-256 for v in full if v>=256}
    lines=subprocess.check_output(["/tmp/q8_all_exchanges20","8",str(k),str(g)],input=" ".join(map(str,p))+"\n",text=True).splitlines()
    best={}
    for l in lines[:-1]:
        marker,*vs=l.split();assert marker=="PATH"
        w=list(map(int,vs));verify(w);assert len(w)==len(p)+g and max(w)<256
        key=min(norm(w),norm(w[::-1]))
        # Count the old upper-arm vertices now forbidden; breaking a bridge costs one more.
        defects=len(U.intersection(w[1:-1]))+sum(v not in U for v in (w[0],w[-1]))
        score=len(full)-1+g-defects
        best[key]=max(score,best.get(key,0))
    return best
if __name__=="__main__":
    bank=collect();candidates={}
    for p,full in bank:candidates[min(norm(p),norm(p[::-1]))]=len(full)-1
    with ProcessPoolExecutor(4) as pool:
        for new in pool.map(mut,((p,f,k,g) for p,f in bank for g in (0,1) for k in (1,2,3,4)),chunksize=1):
            for key,s in new.items():candidates[key]=max(s,candidates.get(key,0))
    rows=sorted(candidates,key=lambda k:(-candidates[k],-len(k),k))
    Path("q8_two_crossing_middle_seeds.txt").write_text("\n".join(rows)+"\n")
    print(json.dumps({"base":len(bank),"new_and_old":len(rows),"compatibility_scores":Counter(candidates.values())}))
