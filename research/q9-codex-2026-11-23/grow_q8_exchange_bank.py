"""Grow long eight-dimensional parents, retaining both canonical rooted orientations."""
from concurrent.futures import ProcessPoolExecutor
from collections import Counter
import json,subprocess
from pathlib import Path
from verify_q9_center_avoidance import verify
def norm(p):
    ren={}
    return "".join(str(ren.setdefault(a^b,len(ren))) for a,b in zip(p,p[1:]))
def collect(job):
    p,k,g=job;new=set()
    lines=subprocess.check_output(["/tmp/q8_all_exchanges20","8",str(k),str(g)],input=" ".join(map(str,p))+"\n",text=True).splitlines()
    for l in lines[:-1]:
        marker,*w=l.split();assert marker=="PATH"
        w=list(map(int,w));verify(w)
        assert max(w)<256 and len(w)==len(p)+g and len(set(p)-set(w))==k
        new.update([norm(w),norm(w[::-1])])
    assert lines[-1].split()[1]=="NO"  # exhaustive mode always continues after emitting a path
    return new
if __name__=="__main__":
    old=set(Path("q8_joint_even_arms.txt").read_text().split())
    bank={}
    for w in sorted(old):
        p=[0]
        for c in w:p.append(p[-1]^1<<int(c))
        key=min(norm(p),norm(p[::-1]));bank.setdefault(key,p)
    jobs=[(p,k,g) for p in bank.values() if len(p)>=96 for g in (0,1) if 96<=len(p)-1+g<=98
          for k in range(1, (5 if len(p)>=97 else 4))]
    new=set()
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(collect,jobs,chunksize=3):new.update(r)
    new.difference_update(old)
    Path("q8_exchange_new_rooted_arms.txt").write_text("".join(w+"\n" for w in sorted(new)))
    print(json.dumps({"tasks":len(jobs),"new_rooted_by_edges":Counter(map(len,new))}))
