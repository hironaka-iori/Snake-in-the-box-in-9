"""Complete a fixed Q8 slice after branching on the lower endpoints."""
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
from collections import Counter
import json,random,sys
from search_q9_free_record_slice import inputs,search,verify

def domain(q,target,missing):
    lower={v for v in q if v<256}
    ds={v:sum((v^(1<<d)) in lower for d in range(8)) for v in lower}
    iso={v for v,d in ds.items() if not d}
    tips={v for v,d in ds.items() if d==1}
    assert set(missing)<=tips
    ends=iso|set(missing)
    if len(ends)>2 or (len(ends)==2 and (sum(v.bit_count() for v in ends)%2!=target%2)):
        return "UNSAT",None
    fixed=lower|{v+256 for v in (tips|iso)-set(missing)}
    allowed=lower|(set(range(256,512))-{v+256 for v in missing})
    budget=10000
    st,w=search(fixed,set(q),target,budget,allowed=allowed)
    if w:
        verify(w);assert len(w)==target+1 and {z for z in w if z<256}==lower
        assert {w[0],w[-1]}&lower==ends
    return st,w

def run(job):
    i,a,s,q,mode=job
    low={v for v in q if v<256}
    ds={v:sum((v^(1<<d)) in low for d in range(8)) for v in low}
    iso={v for v,d in ds.items() if not d}
    tips=sorted(v for v,d in ds.items() if d==1)
    cases=[c for n in range(3-len(iso)) for c in combinations(tips,n)]
    if mode=="sample" and len(cases)>30:
        rng=random.Random(i*903+a*18+s);cand=rng.sample(cases,30)
        cases=list(dict.fromkeys([(),tuple(sorted({q[0],q[-1]}&set(tips))),*cand]))
    counts=Counter()
    for c in cases:
        st,w=domain(q,192,c)
        counts[st]+=1
        if w:return [i,a,s,len(tips),len(iso),len(cases),counts,list(c),w]
    return [i,a,s,len(tips),len(iso),len(cases),counts,None,None]

if __name__=="__main__":
    jobs=list(inputs())
    for i,a,s,q in jobs[::max(1,len(jobs)//10)]:
        low={v for v in q if v<256}
        tips={v for v in low if sum((v^(1<<d)) in low for d in range(8))==1}
        st,w=domain(q,191,tips&{q[0],q[-1]})
        assert st!="UNSAT"
    pending={tuple(r[:3]) for r in map(json.loads,open("q9_free_record_slice_192.jsonl")) if r[4]=="UNKNOWN"}
    if len(sys.argv)>2:
        todo={tuple(r[:3]) for r in map(json.loads,open(sys.argv[2])) if r[3]<=8 or r[4]>0}
        pending &=todo
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(run,((i,a,s,q,sys.argv[1]) for i,a,s,q in jobs if (i,a,s) in pending),chunksize=2):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
