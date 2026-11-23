from sheet import solve,valid,ROOT
from itertools import product
from collections import Counter
import json

def brute(tags,groups,sheet):
    path=[0];best=-1
    def extend(i,last_cross):
        nonlocal best
        if i==len(tags):best=max(best,len(path)-1)
        opts=[] if last_cross else [(sheet,i,True)]
        if i<len(tags):opts += [(a,i+1,False) for a in groups[tags[i]]]
        for a,j,c in opts:
            y=path[-1]^(1<<a)
            if any((y^z).bit_count()<2 for z in path[:-1]):continue
            path.append(y);extend(j,c);path.pop()
    extend(0,False)
    return best
def main():
    groups=[(0,1),(2,3)];sheet=4;count=Counter()
    for n in range(1,8):
        for tags in product(range(2),repeat=n):
            w=[groups[g][0] for g in tags];b=brute(tags,groups,sheet)
            for target in {max(0,b),max(0,b+1)}:
                r,p=solve(w,groups,sheet,target,10000)
                assert (r=='FOUND')==(b>=0 and b>=target) and r!='UNKNOWN',(tags,b,target,r)
                count[r]+=1
    print(json.dumps(dict(test='exhaustive_Q5',counts=count)),flush=True)
    for i,w in enumerate((ROOT/'q9_gap_generations/prior191.words').read_text().split()[:8]):
        import random
        ds=list(range(9));random.Random(456+i).shuffle(ds);s=ds.pop();g=list(zip(ds[::2],ds[1::2]))
        r,p=solve(list(map(int,w)),g,s,191,100000);print(json.dumps(dict(test='191',case=i,status=r,edges=len(p)-1 if p else None,checked=valid(p) if p else None)),flush=True)
if __name__=='__main__':main()
