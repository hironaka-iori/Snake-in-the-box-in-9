"""Repair low-defect walks with arbitrary nine-cube vertices outside fixed intervals."""
import json,glob,random,sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from verify_q9_center_avoidance import verify,forms
from search_q9_anchored_sets import search
def defects(p):
    assert len(set(p))==len(p)
    assert all((v^w).bit_count()==1 for v,w in zip(p,p[1:]))
    return [(i,j) for j,w in enumerate(p) for i,v in enumerate(p[:j-1] if j else []) if (v^w).bit_count()==1]
def inputs():
    seen=set();bank=[]
    for f in sorted(glob.glob("q9_eligible_walk_*.log"))+["q9_near3_diverse_walks.log"]:
        for l in open(f):
            if not l.startswith("NEAR "):continue
            p=list(map(int,l.split()[1:]));key=forms(p,len(p)-1)[0]
            if key in seen:continue
            seen.add(key);bad=defects(p);assert 1<=len(bad)<=3 and len(p)==193
            bank.append((key.hex(),p,bad))
    return sorted(bank,key=lambda r:(len(r[2]),r[0]))
def solve(job):
    key,p,bad,m,rep=job
    rng=random.Random(int(key[:40],16)+rep+31*m)
    # Unlock every chord and nearby intervals; occasionally also unlock disjoint regions.
    indices=set()
    for h,(i,j) in enumerate(bad):
        which=(i,j) if m%3==0 else ((i,) if rep>>h&1 else (j,))
        for v in which:
            width=(3,6,10,16)[m%4]
            indices.update(range(max(0,v-width),min(len(p),v+width+1)))
    for _ in range(m//2):
        c=rng.randrange(len(p));rad=rng.randrange(2,10)
        indices.update(range(max(0,c-rad),min(len(p),c+rad+1)))
    fixed={v for i,v in enumerate(p) if i not in indices}
    st,w=search(fixed,set(p),len(p)-1,15000,at_least=True)
    if w:verify(w);assert len(w)>=len(p) and fixed<=set(w)
    return [key,len(bad),m,rep,len(fixed),st,w]
def control():
    import gzip
    for l in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,l.split()))
        if len(p)!=192:continue
        verify(p)
        for i in range(1,len(p)-1):
            v=p[i-1]^p[i]^p[i+1]
            if v in p:continue
            q=p[:];q[i]=v;bad=defects(q)
            if len(bad)!=1:continue
            fixed=set(q)-{v}
            st,w=search(fixed,set(q),191,20000,at_least=True)
            assert st=="FOUND";verify(w);assert len(w)>=192
            return {"control":191,"initial_chords":bad,"witness":w}
    raise AssertionError
if __name__=="__main__":
    print(json.dumps(control()),flush=True)
    bank=inputs();print(json.dumps({"unique_seeds":len(bank),"defects":[sum(len(z[2])==k for z in bank) for k in (1,2,3)]}),flush=True)
    jobs=[(*z,m,rep) for z in bank for m in (0,1,3,5,7,9) for rep in range(1 if m%3==0 else 2)]
    with ProcessPoolExecutor(2) as pool:
        for z in pool.map(solve,jobs):
            print(json.dumps(z,separators=(",",":")),flush=True)
            if z[-1]:break
