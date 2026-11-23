"""Relax disjoint intervals in the most compatible sampled Q8 layer placements."""
from concurrent.futures import ProcessPoolExecutor
import gzip,json,random
from search_q8_relaxed_pair_placements import placements,search,verify
from verify_q9_center_avoidance import forms

def init():
    global excluded
    excluded=set()
    for name in ("q9_free_bridge_join_inputs.txt.gz","q9_centers_1042_inputs.txt.gz"):
        for line in gzip.open(name,"rt"):excluded.update(forms(list(map(int,line.split())),142))
    assert len(excluded)==17974

def forbidden(p):
    for i,f in enumerate(forms(p,142)):
        if f in excluded:return p[i:i+143]

def job(row):
    i,j,pi,t,p,q,n=row
    results=[]
    for variant,count in enumerate((3,4,5)):
        rng=random.Random(321471+i*2917+j*17+pi*51+t+variant)
        a=set()
        for arm in (p,q):
            # Use one short interval in each of several disjoint bins.
            for at in range(count):
                left,right=at*len(arm)//count,(at+1)*len(arm)//count
                width=rng.randint(9,min(16,right-left))
                pos=rng.randint(left,right-width)
                a.update(arm[pos:pos+width])
        for w in range(256):
            if w in a and w+256 in a:a.remove(w+256 if rng.getrandbits(1) else w)
        for target in (192,191,190,189):
            st,w=search(a,set(p+q),target,3200,reject_fragment=forbidden)
            if w:
                verify(w);assert len(w)==target+1 and a<=set(w) and not forbidden(w)
            results.append([i,j,pi,t,variant,len(a),target,st,w])
            if w:break
    return results

if __name__=="__main__":
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for result in pool.map(job,placements(),chunksize=2):
            for row in result:
                print(json.dumps(row,separators=(",",":")),flush=True)
                if row[6]==192 and row[-1]:raise SystemExit
