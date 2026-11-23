import json,os,sys
from concurrent.futures import ProcessPoolExecutor
from search_q9_long_arm_anywhere import arms
from search_q9_shell_dual import solve
from verify_q9_center_avoidance import verify
def revisit(job):
    k,arm,ep,g=job
    fixed=set(arm)
    deg={v:sum(v^1<<d in fixed for d in range(8)) for v in fixed}
    domain=fixed|{v+256 for v in range(256) if deg.get(v,0)<2}
    domain.update(v for v in range(256) if all(deg[x]<2 for x in fixed if (x^v).bit_count()==1) and sum(v^1<<d in fixed for d in range(8))<=2)
    r=solve((0,arm,0,ep,g,1900000,fixed,domain))
    if r[-1]:verify(r[-1]);assert fixed<=set(r[-1])
    return [k,ep,g,*r[4:]]
if __name__=="__main__":
    bank={k.hex():v for k,v in arms()}
    seen=set()
    for f in sys.argv[1:]:
        for l in open(f):seen.add(tuple(json.loads(l)[:3]))
    raw=[json.loads(l) for l in open("q9_long_arm_anywhere_atleast192.jsonl")]
    jobs=[(k,bank[k],e,g) for k,e,g,s,u,w in raw if s=="UNKNOWN" and (k,e,g) not in seen]
    with ProcessPoolExecutor(2) as pool:
        for r in pool.map(revisit,jobs):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
