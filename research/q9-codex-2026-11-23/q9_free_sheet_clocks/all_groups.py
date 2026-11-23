from sheet import solve,ROOT
import json,sys,random
from collections import Counter
from pathlib import Path
def match(ds):
    if not ds:
        yield []
        return
    a,*tail=ds
    for b in tail:
        for sub in match([x for x in tail if x!=b]):yield [(a,b),*sub]
def main():
    f,idx,target,cap=sys.argv[1:]
    source=(ROOT/f).read_text().split()[int(idx)]
    jobs=[(s,g) for s in range(9) for g in match([a for a in range(9) if a!=s])]
    random.Random(4311).shuffle(jobs);stats=Counter()
    for s,g in jobs:
        st,p=solve(list(map(int,source)),g,s,int(target),int(cap));stats[st]+=1
        print(json.dumps(dict(sheet=s,pairs=g,status=st,path=p)),flush=True)
        if p:break
    print(json.dumps(dict(done=True,source=source,target=int(target),counts=stats)),flush=True)
if __name__=='__main__':main()
