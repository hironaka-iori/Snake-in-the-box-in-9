from collections import Counter
from functools import lru_cache
from pathlib import Path
import gzip,json,random,sys
from prepare import D,R,unhex,ashex,paircheck
from run import solve
def load():
    return {int(t[1]):list(map(int,t[2:])) for l in (R/'q8_registered_donor_clusters.txt').open() if (t:=l.split())}
def sample(line,ar,br):
    # Protections are based on host order. All non-retained overlaps lose a twin,
    # and at most one crossing stays, so the fragments are acyclic.
    rng=random.Random(50876819+line)
    host=set(ar+br);overlap=sorted(set(ar)&{v-256 for v in br}); fixed=set(host);protect=set()
    rng.shuffle(overlap)
    for j,x in enumerate(overlap):
        if j==0 and line%2:
            for v,route in ((x,ar),(256+x,br)):
                loc=route.index(v)
                if 0<loc<len(route)-1:fixed.discard(route[loc+rng.choice((-1,1))])
                protect.add(v)
        else:
            if line%4==0 and rng.randrange(3)==0:fixed.difference_update((x,x+256))
            else:fixed.discard(x+256*rng.randrange(2))
    protect&=fixed
    return protect|set(rng.sample(sorted(fixed-protect),145-len(protect))),host,len(overlap)
def run():
    bank=load();counts=Counter()
    @lru_cache(maxsize=20000)
    def right(b,k):
        p=list(map(int,k));return [sum(1<<p[d] for d in range(8) if v>>d&1) for v in bank[b]]
    with gzip.open(D/'allhosts.jsonl.gz','wt',compresslevel=3) as out:
        for ln,l in enumerate((R/'q8_near_host_placements.log').open(),1):
            if not l.startswith('HOST '):continue
            _,a,b,t,k,pm=l.split();a,b,t,k=map(int,[a,b,t,k]);br=[256+(x^t) for x in right(b,pm)]
            fixed,host,actual=sample(ln,bank[a],br);assert actual==k and len(fixed)==145
            st,w=solve('minicard',fixed,host,192,5000);counts[st]+=1
            if w:paircheck(w);assert fixed<=set(w) and len(w)>=193
            print(json.dumps([ln,ashex(fixed),st,w],separators=(',',':')),file=out)
            if sum(counts.values())%5000==0:print(json.dumps(dict(counts)),flush=True)
            if w:break
    print(json.dumps(dict(done=dict(counts))),flush=True)
if __name__=='__main__':run()
