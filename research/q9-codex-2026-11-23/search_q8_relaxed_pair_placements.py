"""Sample relative Q8 placements, then allow arbitrary Q9 vertices outside both parents."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import permutations
import json
import random
import numpy as np
from search_q9_anchored_sets import search,NB
from verify_q9_center_avoidance import forms,verify

def bank():
    classes={}
    for line in open("q8_joint_even_arms.txt"):
        p=[0]
        for c in line.strip():p.append(p[-1]^(1<<int(c)))
        key=forms(p,len(p)-1)[0]
        if key not in classes:classes[key]=p
    return list(classes.values())

def placements():
    rng=random.Random(886425); paths=bank()
    dims=np.array(rng.sample(list(permutations(range(8))),1024))
    lut=np.zeros((len(dims),256),dtype=np.uint8)
    for v in range(1,256):
        low=v&-v
        lut[:,v]=lut[:,v^low]^(1<<dims[:,low.bit_length()-1])
    def packed(mask):
        return np.packbits(mask,axis=1,bitorder="little").copy().view(np.uint64)
    lay=[];up=[]
    selected=[]
    for length in range(93,99):
        ids=[i for i,p in enumerate(paths) if len(p)==length+1]
        selected.extend(rng.sample(ids,min(12,len(ids))))
    for i in selected:
        p=paths[i];verify(p);a=np.zeros((256,256),dtype=np.uint8)
        a[np.arange(256)[:,None],np.arange(256)[:,None]^p]=1
        lay.append(packed(a));b=np.zeros((len(dims),256),dtype=np.uint8)
        b[np.arange(len(dims))[:,None],lut[:,p]]=1;up.append(packed(b))
    for u,i in enumerate(selected):
        for z in range(u,len(selected)):
            j=selected[z];p=paths[i];q=paths[j]
            if len(p)+len(q)<193:continue
            intersections=np.bitwise_count(up[z][:,None,:]&lay[u][None,:,:]).sum(axis=2,dtype=np.int16)
            # Random tie breaks among the smallest overlap counts.
            rank=intersections.astype(np.int64)*1000000+np.random.default_rng(i*2459+j).integers(0,1000000,intersections.shape)
            for ix in np.argpartition(rank.ravel(),3)[:4]:
                pi,t=divmod(int(ix),256)
                v=[256+(int(a)^t) for a in lut[pi,q]]
                yield i,j,pi,t,p,v,int(intersections[pi,t])

def job(row):
    i,j,pi,t,p,q,overlap=row
    original=set(p+q);collide=set(p)&{v^256 for v in q}
    assert len(collide)==overlap
    rng=random.Random(83147+i*101+j*3+pi+t)
    out=[]
    for variant in range(4):
        fixed=set(original)
        for w in sorted(collide):
            if variant==0:fixed.difference_update([w,w+256])
            else:fixed.remove(w if rng.getrandbits(1) else w+256)
        if variant>=2:
            for arm in (p,q):
                for _ in range(2 if variant==2 else 4):
                    k=rng.randrange(len(arm)-5)
                    fixed.difference_update(arm[k:k+5])
        st,w=search(fixed,original,192,5000)
        if w:verify(w);assert len(w)==193 and fixed<=set(w)
        out.append([i,j,pi,t,overlap,variant,len(fixed),st,w])
        if w:break
    return out

if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("--workers",type=int,default=4)
    opt=ap.parse_args()
    with ProcessPoolExecutor(opt.workers) as pool:
        for group in pool.map(job,placements(),chunksize=2):
            for row in group:
                print(json.dumps(row,separators=(",",":")),flush=True)
                if row[-1]:raise SystemExit
