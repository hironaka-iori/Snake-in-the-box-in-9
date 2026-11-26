"""Seek a 93-edge arm after deleting sites of the common 92-edge seed in a small number of runs."""
from itertools import combinations
from collections import Counter
from near import HERE, sources, assemble, valid, shape, write,ArgumentParser

def patterns(n,r):
    for left in range(n-r+1):
        yield tuple(range(left,left+r))
    for first in range(1,r):
        second=r-first
        for a in range(n-r):
            for b in range(a+first+1,n-second+1):
                yield tuple(range(a,a+first))+tuple(range(b,b+second))

def main():
    cli=ArgumentParser();cli.add_argument("--omissions",type=int,default=4);args=cli.parse_args()
    r=args.omissions; seed=bytes(sources()["common92"]["seed"]);byshape={};checked=0;hist=Counter()
    for omit in patterns(len(seed),r):
        checked+=1
        for p in sorted(assemble(seed,omit,93,98)):
            assert len(set(seed)-set(p))==r
            valid(p,8); s=shape(p);hist[len(p)-1]+=1
            row=byshape.setdefault(s,dict(path=list(p),minimum_omissions=r,placements=0,example_omitted=list(omit)))
            row["placements"]+=1
    out=dict(seed=list(seed),minimum=93,maximum=98,omissions=r,maximum_runs=2,omission_patterns=checked,
             histogram=hist,shapes=byshape)
    write(HERE/("common92-runs-"+str(r)+".json"),out)
    print("common92",r,checked,dict(hist),"shapes",len(byshape),flush=True)
if __name__=="__main__":main()
