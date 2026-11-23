"""Complete Q8 slices from record snakes with a free opposite Q8 layer."""
from concurrent.futures import ProcessPoolExecutor
import gzip,json,sys
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import verify,forms

def parents():
    bank={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192:bank.setdefault(forms(p,191)[0],p)
    assert len(bank)==131
    return list(bank.values())

def normalize(p,axis,side):
    # Compress the eight remaining coordinates. The fixed slice is layer zero.
    def image(x):
        v=x^p[0]
        return ((v>>(axis+1))<<axis)|(v&((1<<axis)-1))|((((v>>axis)&1)^side)<<8)
    return [image(v) for v in p]

def inputs():
    seen=set()
    for i,p in enumerate(parents()):
        verify(p)
        for axis in range(9):
            for side in (0,1):
                q=normalize(p,axis,side)
                mask=sum(1<<v for v in q if v<256)
                if mask not in seen:
                    seen.add(mask);yield i,axis,side,q

def compute(job):
    i,axis,side,q,target,budget=job
    fixed={v for v in q if v<256}
    domain=fixed|set(range(256,512))
    st,w=search(fixed,set(q),target,budget,allowed=domain)
    if w:
        verify(w);assert len(w)==target+1 and {v for v in w if v<256}==fixed
    return [i,axis,side,len(fixed),st,w]

if __name__=="__main__":
    budget=int(sys.argv[1])
    pending=None
    if len(sys.argv)>2:
        pending={tuple(r[:3]) for r in map(json.loads,open(sys.argv[2])) if r[4]=="UNKNOWN"}
    jobs=list(inputs())
    if pending is None:
        recovered=0
        for i,axis,side,q in jobs[::max(1,len(jobs)//8)]:
            verify(q)
            answer=compute((i,axis,side,q,191,50000))
            assert answer[4] in ("FOUND","UNKNOWN")
            recovered+=answer[4]=="FOUND"
        assert recovered>0
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(compute,((i,a,b,q,192,budget) for i,a,b,q in jobs
                                   if pending is None or (i,a,b) in pending),chunksize=3):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
