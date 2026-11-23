"""Cross two projected record paths at a shared ordered motif and refill the square fibers."""
import argparse
import json
import random
from collections import Counter, defaultdict
from itertools import combinations
from search_q9_flexible_corners import solve
from search_q9_square_fiber_lift import projections
from search_q9_two_flexible_ends import verify
from search_q9_projected_reversal import normalized


def signature(word):
    labels={}
    motif=bytes(labels.setdefault(x,len(labels)) for x in word)
    return motif,list(labels)

def transform(directions, rng):
    missing=list(set(range(7))-set(directions))
    rng.shuffle(missing)
    dims=directions+missing
    return [sum(1<<j for j,bit in enumerate(dims) if x&(1<<bit)) for x in range(128)]

def generate(bank_path, attempts):
    base={}
    for line in open(bank_path):
        n,*steps=map(int,line.split())
        assert n==9 and len(steps)==191
        v=[0]
        for d in steps:v.append(v[-1]^(1<<d))
        verify(v,191)
        for word in [steps,steps[::-1]]:
            for p,h in projections(word):
                base.setdefault(bytes(p), h)
    rng=random.Random(2001192)
    table=defaultdict(list)
    records=list(base.items())
    for idx,(p,h) in enumerate(records):
        changes=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
        for cut in rng.sample(range(22,len(changes)-20),10):
            motif,dims=signature(changes[cut-9:cut+3])
            table[motif].append((idx,cut,dims))
    groups=[members for members in table.values() if len(members)>1]
    known={min(normalized(p),normalized(p[::-1])) for p in base}
    scored={};tried=set();counts=Counter()
    for _ in range(attempts):
        ra,rb=rng.sample(rng.choice(groups),2)
        ia,i,da=ra;ib,j,db=rb
        if ia==ib:continue
        a,ha=records[ia];b,hb=records[ib]
        pre=ha[:i+1];post=hb[j+1:]
        vertices=sum(map(len,pre))+sum(map(len,post))
        if not 192<=vertices<=204:continue
        ta=transform(da,rng);tb=transform(db,rng)
        shift=ta[a[i]]^tb[b[j]]
        q=bytes([ta[x] for x in a[:i+1]]+[tb[x]^shift for x in b[j+1:]])
        key=min(normalized(q),normalized(q[::-1]))
        if key in known:continue
        variation=(ia,i,ib,j,shift,tuple(tb))
        if variation in tried:continue
        tried.add(variation)
        prefix=[v+128*c for v,colors in zip(q,pre) for c in colors]
        mask=Counter()
        for x in prefix:
            mask[x]+=10
            for d in range(9):mask[x^(1<<d)]+=1
        for swap in [False,True]:
            f=lambda x: (2*(x&1)+(x>>1)) if swap else x
            delta=pre[-1][-1]^f(hb[j][-1])
            colors=pre+[[f(x)^delta for x in l] for l in post]
            suffix=[v+128*c for v,layer in zip(q[len(pre):],colors[len(pre):]) for c in layer]
            assert (prefix[-1]^suffix[0]).bit_count()==1
            cost=sum(mask[x] for x in suffix)-1
            counts["embeddings"]+=1
            quality=(cost,abs(vertices-193))
            if key not in scored or quality<scored[key][0]:
                scored[key]=(quality,q,colors,i)
            if cost==0 and vertices>=193:
                w=prefix+suffix;verify(w,192)
                return [],w,counts
    counts["new_projections"]=len(scored)
    return sorted(scored.values(),key=lambda v:v[0]),None,counts

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--bank",default="/tmp/q9_project_records_input9")
    ap.add_argument("--attempts",type=int,default=120000)
    ap.add_argument("--limit",type=int,default=3000)
    args=ap.parse_args()
    cases,w,stats=generate(args.bank,args.attempts)
    print(json.dumps(["GENERATION",dict(stats),w]),flush=True)
    if not w:
        for quality,q,h,cut in cases[:args.limit]:
            q=bytes(v^q[0] for v in q)
            root=h[0][0];h=[[x^root for x in group] for group in h]
            ids=list(range(1+(cut%2),len(q)-1,2))
            status,w=solve(q,h,ids,192,2200,True)
            if w:verify(w,192)
            print(json.dumps([status,q.hex(),cut,quality,w],separators=(",",":")),flush=True)
            if w:break
