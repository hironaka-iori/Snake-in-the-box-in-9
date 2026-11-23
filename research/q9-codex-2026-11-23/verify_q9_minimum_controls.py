"""Independent ordered-path oracle on random induced Q4 subgraphs."""
import json,os,random
from collections import Counter
from search_q9_shell_dual import solve
from verify_q9_center_avoidance import verify
def oracle(domain,fixed,g,e):
    def walk(p):
        if len(p)-1>=g and (len(p)-1-g)%2==0 and fixed<=set(p) and (g%2 or p[0].bit_count()%2==e):return p
        for d in range(4):
            y=p[-1]^1<<d
            if y in domain and y not in p and all((y^x).bit_count()!=1 for x in p[:-1]):
                q=walk(p+[y])
                if q:return q
    return next((q for x in domain if (q:=walk([x]))),None)
if __name__=="__main__":
    assert os.getenv("Q9_PATH_MINIMUM")
    rng=random.Random(118812);counts=Counter();above=0
    for i in range(96):
        D={x for x in range(16) if rng.random()<0.85};F=set(rng.sample(sorted(D),min(i%6,len(D))))
        g=3+i%5;e=(i//3)%2;w=oracle(D,F,g,e)
        r=solve((i,[],0,e,g,300000,F,D));assert r[4]!="UNKNOWN" and bool(r[-1])==bool(w),(r,w)
        if r[-1]:verify(r[-1]);above+=len(r[-1])-1>g
        counts[r[4]]+=1
    assert counts["FOUND"] and above
    print(json.dumps({"Q4_cases":96,"outcomes":counts,"returned_above_threshold":above}))
