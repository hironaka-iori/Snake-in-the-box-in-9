from insertion import solve
from search import validate,axes,D
import random,json,sys
from collections import Counter
def run(n,total,q,seed):
    rng=random.Random(seed);ws=[list(map(int,w)) for w in (D.parent/'q9_gap_generations/prior191.words').read_text().split()]
    raw=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    stats=Counter()
    for t in range(total):
        if t%2==0:
            w=rng.choice(ws).copy();start=rng.randint(0,186);size=rng.choice([1,2,3,4]);stop=start+size
            out=w[start:stop];del w[start:stop];dest=rng.randrange(len(w)+1)
            if rng.getrandbits(1):out.reverse()
            w[dest:dest]=out
            while len(w)<n-1:w.insert(rng.randrange(len(w)+1),rng.randrange(9))
        else:
            w=rng.choice(raw).copy();p=axes(w);bad=[(i,j) for j,v in enumerate(p) for i,u in enumerate(p[:max(0,j-1)]) if (u^v).bit_count()<2]
            i,j=rng.choice(bad);h=min(len(w)-1,max(0,rng.choice([i,j])+rng.randrange(-2,3)));w.pop(h)
        dims=list(range(9));rng.shuffle(dims);ps=[tuple(dims[j:j+2]) for j in range(0,8,2)];s=dims[-1];e=rng.randrange(5)
        st,p,h,c=solve(w,ps,s,e,q);stats[st]+=1
        if p:assert validate(p) and len(p)==n+1;print(json.dumps(dict(found=p,source=w,seam=h)),flush=True);break
        if t%25==24:print(json.dumps(dict(tested=t+1,counts=stats)),flush=True)
    print(json.dumps(dict(done=True,counts=stats)),flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
