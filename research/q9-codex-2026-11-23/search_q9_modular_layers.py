"""Find open paths as induced subgraphs of cyclic-labelling domains."""
from concurrent.futures import ProcessPoolExecutor
import itertools,json,random
from search_q9_contact_shell import solve as unused
from verify_q9_center_avoidance import verify
from search_q9_anchored_sets import search

def make_domains():
    rng=random.Random(25931)
    jobs=[]
    for modulus in (7,8,9,10,11,12,13,14,15,16):
        for trial in range(40):
            weights=[rng.randrange(1,1+modulus//2) for _ in range(9)]
            mask=set(rng.sample(range(modulus),rng.choice([modulus//2,modulus//2+1])))
            points={v for v in range(512) if sum(w for i,w in enumerate(weights) if v>>i&1)%modulus in mask}
            if len(points)<193:continue
            jobs.append((modulus,weights,sorted(mask),points))
    return jobs
def run(job):
    mod,ws,mask,D=job
    # Iteratively cap every path by peeling pendant branches, splitting on component boundaries.
    neigh={v:{v^1<<i for i in range(9)}&D for v in D}
    und=D.copy();cc=[]
    while und:
        comp=[und.pop()]
        for v in comp:
            for x in neigh[v]&und:und.remove(x);comp.append(x)
        if len(comp)>=193:cc.append(comp)
    if not cc:return [mod,ws,mask,len(D),"COMPONENT_CAP",0,None]
    old=random.Random(sum(ws)*mod+len(D))
    best=[]
    for comp in cc:
        A=set(comp)
        for t in range(12):
            w=[old.choice(comp)];free=A-{w[0]}
            while True:
                feasible=neigh[w[-1]]&free
                if not feasible:break
                v=max(sorted(feasible),key=lambda u:old.random()*4+len(neigh[u]&free)-0.25*len(neigh[w[-1]]&free&neigh[u]))
                free-=neigh[w[-1]];w.append(v)
            if len(w)>len(best):best=w
        verify(best)
        if len(best)>=193:return [mod,ws,mask,len(D),"FOUND",len(best)-1,best]
        if len(best)<65:continue
        # Require separated fragments of the best greedy walk; search for a different ordering and length.
        blocks={best[j] for j in range(len(best)) if (j//9)%3==0}
        st,w=search(blocks,set(best),192,12000,allowed=A,at_least=True)
        if w:verify(w);return [mod,ws,mask,len(D),st,len(best)-1,w]
    return [mod,ws,mask,len(D),"SAMPLED",len(best)-1,None]
if __name__=="__main__":
    with ProcessPoolExecutor(3) as p:
        for r in p.map(run,make_domains(),chunksize=1,buffersize=20):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
