from novel import lift
from search import D,validate,axes
from relay import shape
from collections import Counter
import random,json,sys
def run(total,seed,cap,ctrl):
    rng=random.Random(seed);real=[list(map(int,w)) for w in (D.parent/'q9_gap_generations/prior191.words').read_text().split()]
    ref={shape(w) for w in real};all_orient=[z for w in real for z in [w,w[::-1]]]
    near=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split()]
    stats=Counter();new=set()
    for t in range(total):
        row=rng.randrange(len(real));w=real[row].copy()
        if t%3 and not ctrl:
            long=rng.choice(near);k=rng.randrange(len(long)-190);w=long[k:k+191]
        blocked=[z for z in all_orient if not ctrl or shape(z)!=shape(real[row])]
        ds=list(range(9));rng.shuffle(ds);ps=[tuple(ds[i:i+2]) for i in range(0,8,2)];s=ds[-1]
        st,p,c=lift(w,ps,s,cap,blocked);stats[st]+=1
        if p:
            assert validate(p) and len(p)==192
            key=shape([(a^b).bit_length()-1 for a,b in zip(p,p[1:])]);assert key not in ref or ctrl and key==shape(real[row])
            if key not in new:
                new.add(key);tips=[[q[-1]^1<<d for d in range(9) if all((v^q[-1]^1<<d).bit_count()>1 for v in q[:-1])] for q in (p[::-1],p)]
                print(json.dumps(dict(candidate=key,known=key in ref,ends=tips,witness=p)),flush=True)
                if any(tips):
                    longer=([tips[0][0]]+p if tips[0] else p+[tips[1][0]]);assert validate(longer)
                    print(json.dumps(dict(found=longer)),flush=True);break
        if t%50==49:print(json.dumps(dict(tested=t+1,counts=stats,classes=len(new))),flush=True)
    print(json.dumps(dict(done=True,counts=stats,classes=len(new))),flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
