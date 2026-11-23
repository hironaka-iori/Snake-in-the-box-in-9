"""Check case identifiers, independent affine-subspace counts and solver outcomes."""
from collections import Counter
from itertools import combinations, zip_longest
import json
from pathlib import Path
from search_q9_remaining_flats import read_cuts, spaces

def independent_count(ruled, rank):
    allowed = {z for z in range(1024) if z & 511 and z not in ruled}
    # Each rank-two affine system contains a unique increasing triple of signed normals.
    pairs = [(x,y) for x,y in combinations(sorted(allowed),2) if (x^y)>y and (x^y) in allowed]
    if rank == 2:
        return len(pairs)
    # Each rank-three system extends seven distinct planes in four ways apiece.
    extensions = 0
    for x,y in pairs:
        xy = x^y
        extensions += sum((z^x) in allowed and (z^y) in allowed and (z^xy) in allowed for z in allowed)
    assert extensions % 28 == 0
    return extensions//28

def audit(prefix,rank,retry=None):
    manifest=json.load(open(prefix+"_manifest.json"))
    cuts,hashes=read_cuts(manifest["inputs"])
    counts=Counter()
    pending=set()
    expected=((i,list(b)) for i,blocked in enumerate(cuts) for b in spaces(blocked,rank))
    with open(prefix+"_results.jsonl") as stream:
        for exp,r in zip_longest(expected,map(json.loads,stream)):
            assert exp is not None and r is not None
            i,b,out,w=r
            assert (i,b)==exp and out in ("UNSAT","UNKNOWN") and w is None
            counts[out]+=1
            if out=="UNKNOWN":pending.add((i,tuple(b)))
    independent=[independent_count(c,rank) for c in cuts]
    assert all(n==manifest["counts"].get(str(i),0) for i,n in enumerate(independent))
    assert sum(independent)==sum(counts.values())==manifest["total"]
    if retry and Path(retry).exists():
        seen=set()
        for i,b,st,w in map(json.loads,open(retry)):
            k=i,tuple(b)
            assert k in pending and k not in seen and w is None and st in ("UNSAT","UNKNOWN")
            seen.add(k)
            if st=="UNSAT":counts["UNSAT"]+=1;counts["UNKNOWN"]-=1
    if rank==2:
        import search_q9_flat_split as split1
        import search_q9_flat_split_deep as split2
        split1.init()
        pending={(i,tuple(b)) for i,b,st,w in map(json.loads,open(retry)) if st=="UNKNOWN"}
        children={(i,b,c) for i,b in pending for c in range(1<<len(split1.split(i,b)[2]))}
        leaves=set()
        for i,b,c,st,w in map(json.loads,open("q9_codim2_splits.jsonl")):
            k=i,tuple(b),c
            children.remove(k)
            assert w is None and st in ("UNKNOWN","UNSAT")
            if st=="UNKNOWN":leaves.add(k)
        assert not children
        terminal={(i,b,c,d) for i,b,c in leaves for d in range(1<<len(split2.prep(i,b,c)[2]))}
        for i,b,c,d,st,w in map(json.loads,open("q9_codim2_splits_deep.jsonl")):
            terminal.remove((i,tuple(b),c,d))
            assert st=="UNSAT" and w is None
        assert not terminal and counts["UNKNOWN"]==len(pending)
        counts["UNSAT"]+=counts.pop("UNKNOWN")
    return dict(parent_count=len(cuts),patch_dimension=9-rank,surviving_flat_tests=sum(independent),
                results=dict(counts),input_sha256=hashes,manifest=prefix+"_manifest.json")
if __name__=="__main__":
    print(json.dumps([audit("q9_remaining_codim3",3),audit("q9_codim2_allcuts",2,"q9_codim2_allcuts_retry.jsonl")],indent=2))
