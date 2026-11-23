"""Compare local-cube enumeration with a direct vertex-based SAT encoding."""
import json,random,sys
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from search_q9_parity_cut_cubes import solve,parents
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import verify

def check(row):
    i,p,m,s,target,at_least=row
    fixed={v for v in p if (v&m).bit_count()%2==s}
    free={v for v in range(512) if (v&m).bit_count()%2!=s}
    a,w=solve(p,m,s,target,60000,at_least=at_least)
    b,z=search(fixed,set(p),target,60000,allowed=fixed|free,at_least=at_least)
    for witness in [w,z]:
        if witness:
            verify(witness);assert len(witness)>=target+1 and (at_least or len(witness)==target+1)
            assert {v for v in witness if v not in free}==fixed
    assert a==b or "UNKNOWN" in (a,b)
    return [i,m,s,target,len(w)-1 if w else None,len(z)-1 if z else None,a,b]

if __name__=="__main__":
    at_least='--at-least' in sys.argv
    rng=random.Random(1929042);bank=parents();jobs=[]
    for i in range(120):
        q=rng.choice(bank)
        if i%4==0:q=q[1:-1]
        m=rng.choice([m for m in range(511) if m.bit_count()==8-i%3]);s=rng.randrange(2)
        target=len(q)-1 if i%2==0 else 192
        if at_least and i%8==0:target-=5
        jobs.append((i,q,m,s,target,at_least))
    with ProcessPoolExecutor(4) as pool:rows=list(pool.map(check,jobs,chunksize=2))
    summary=Counter((x[-2],x[-1]) for x in rows)
    assert summary["FOUND","FOUND"] and summary["UNSAT","UNSAT"]
    print(json.dumps(dict(cases=rows,results={a+"/"+b:n for (a,b),n in summary.items()})))
