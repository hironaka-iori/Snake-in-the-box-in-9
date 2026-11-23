from check import brute
from mobile import search,ROOT,valid
from itertools import product
from collections import Counter
import json
from random import Random
def main():
    cnt=Counter();rng=Random(2179);g=[(0,1),(2,3)]
    for n in range(1,8):
        for tags in product(range(2),repeat=n):
            off=rng.randrange(2);sw=list(range(off,n-1,2));best=-1
            for bits in product((0,1),repeat=len(sw)):
                v=list(tags)
                for i,on in zip(sw,bits):
                    if on:v[i],v[i+1]=v[i+1],v[i]
                best=max(best,brute(v,g,4))
            w=[g[t][0] for t in tags]
            for target in {max(0,best),max(0,best+1)}:
                st,p=search(w,g,4,target,sw,50000);assert st==('FOUND' if best>=target else 'UNSAT'),(tags,sw,target,best,st)
                cnt[st]+=1
    print(json.dumps(dict(small=cnt)),flush=True)
    for w in (ROOT/'q9_gap_generations/prior191.words').read_text().split()[:10]:
        w=list(map(int,w));ds=list(range(9));rng.shuffle(ds);s=ds.pop();g=list(zip(ds[::2],ds[1::2]));m=len(w)-w.count(s)
        sw=sorted(rng.sample(list(range(0,m-1,2)),10));st,p=search(w,g,s,191,sw,50000);print(json.dumps(dict(status=st,path=p)),flush=True)
if __name__=='__main__':main()
