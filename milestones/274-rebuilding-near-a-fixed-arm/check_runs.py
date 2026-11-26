"""Recompute the saved two-run searches by growing occupied sets instead of ordered components."""
from collections import Counter
from near import HERE,read,write,shape,sources,valid
from replay_near import _enumerate_mask
from near_tip import patterns
def main():
    seed=sources()["common92"]["seed"];original=sum(1<<v for v in seed);results={}
    for f in sorted(HERE.glob("common92-runs-[0-9]*.json")):
        d=read(f);r=d["omissions"];counts=Counter();paths=Counter();done=0
        for omitted in patterns(len(seed),r):
            done+=1
            kept=original ^ sum(1<<seed[i] for i in omitted)
            for p in _enumerate_mask(original,kept,94,99):
                valid(p,8);counts[str(len(p)-1)]+=1;paths[shape(p)]+=1
        assert dict(counts)==d["histogram"] and dict(paths)=={s:v["placements"] for s,v in d["shapes"].items()} and done==d["omission_patterns"]
        results[str(r)]=dict(patterns=done,counts=counts,shape_count=len(paths))
    write(HERE/"common92-two-run-replay.json",results)
    print(results,flush=True)
if __name__=="__main__":main()
