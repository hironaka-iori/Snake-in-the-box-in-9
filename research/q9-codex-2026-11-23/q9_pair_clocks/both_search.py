from biends import lift
from search import D,axes,validate,partition
from collections import Counter
import random,sys,json
def run(total,seed,cap):
    rng=random.Random(seed)
    real=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
    near=(D.parent/'q9_via_q10/monotone_near.words').read_text().split()
    bank=set()
    for w in real+near:
        for j in range(len(w)-190+1):bank.add(w[j:j+190])
    bank=sorted(bank);counts=Counter()
    for t in range(total):
        w=list(map(int,rng.choice(bank)))
        if t%3==2:
            loc=rng.randrange(1,188);gap=rng.randrange(1,4);w[loc:loc+gap+1]=w[loc+1:loc+gap+1]+w[loc:loc+1]
        dims=list(range(9));rng.shuffle(dims);ps=[tuple(dims[j:j+2]) for j in range(0,8,2)];s=dims[-1]
        st,p,k=lift(w,ps,s,cap);counts[st]+=1
        if p:
            print(json.dumps(dict(found=p,core=len(w),source=w,pairs=ps,single=s)),flush=True);break
        if t%50==49:print(json.dumps(dict(tested=t+1,counts=counts)),flush=True)
    print(json.dumps(dict(done=True,counts=counts)),flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
