"""Free the choices within same-color xor pairs and reconstruct a connected Q9 snake."""
import argparse
import gzip
import json
import random
from itertools import combinations
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import verify, forms


def instance(path, minority, t, fraction, target, budget, rng, selectors=False):
    side = set(minority)
    partners = sorted((x, x ^ t) for x in side if (x ^ t) not in side)
    rng.shuffle(partners)
    count = (len(partners)*fraction + 99)//100
    pairs = partners[:count]
    fixed = side - {a for a,_ in pairs}
    allowed = side | {b for _,b in pairs} | {x for x in range(512)
                if (x^minority[0]).bit_count()%2}
    if not fixed:
        raise ValueError("need an anchored minority vertex")
    if selectors:
        from q9_pair_selector import search as solve_pairs
        st,w=solve_pairs(side,pairs,t,set(path),target,budget)
    else:
        st,w=search(fixed,set(path),target,budget,allowed=allowed,exactly_one_pairs=pairs)
    if w is not None:
        verify(w)
        assert len(w)==target+1 and fixed<=set(w)<=allowed
        assert all((a in w)+(b in w)==1 for a,b in pairs)
    return st,w,len(pairs)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("start",type=int);ap.add_argument("stop",type=int)
    ap.add_argument("--fraction",type=int,default=60)
    ap.add_argument("--budget",type=int,default=1500)
    ap.add_argument("--per-side",type=int,default=4)
    ap.add_argument("--selectors",action="store_true")
    args=ap.parse_args()
    paths={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192:
            key=forms(p,191)[0]
            if key not in paths:verify(p);paths[key]=p
    masks=[t for t in range(1,512) if t.bit_count() in (2,4)]
    for i,p in enumerate(paths.values()):
        if not args.start<=i<args.stop:continue
        if i==args.start:
            q=p[:-1];s,w,_=instance(q,q[1::2],3,0,190,10000,random.Random(0),args.selectors)
            assert s=="FOUND" and w
        for side in (0,1):
            rng=random.Random(4819215+i*37+side)
            for t in rng.sample(masks,args.per_side):
                st,w,size=instance(p,p[side::2],t,args.fraction,192,args.budget,rng,args.selectors)
                print(json.dumps([i,side,t,size,st,w],separators=(",",":")),flush=True)
                if w:return


if __name__=="__main__":main()
