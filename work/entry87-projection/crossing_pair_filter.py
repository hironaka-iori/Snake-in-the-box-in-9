"""Necessary conditions on two crossing addresses in the balanced two-for-two exchange."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from punctured_lift import project
from solve import BANK,BANK_HASH,sha256,save


def pair_rows(W):
    W=set(W);holes=set(range(256))-W
    N=[{v^(1<<i) for i in range(8)} for v in range(256)]
    D=[v for v in range(256) if len(N[v]&W)<=4]
    rows=[]
    for r,s in combinations(D,2):
        if s in N[r]:continue
        common=N[r]&N[s]
        required=common&W
        if len(required)>2:continue
        pair={r,s};mandatory_add=pair-W
        # Each selected root has one or two projected neighbours. Shared
        # neighbours must be omitted by the 65-vertex middle-arm bound.
        def choices(source,mandatory,forbidden):
            pool=source-forbidden-mandatory
            def kind(v):return (int(v in N[r]),int(v in N[s]),int(v.bit_count()%2==0))
            classes=Counter(kind(v) for v in pool)
            def add(a,b):return tuple(x+y for x,y in zip(a,b))
            forced=(0,0,0)
            for v in mandatory:forced=add(forced,kind(v))
            missing=2-len(mandatory)
            if missing==0:return Counter({forced:1})
            if missing==1:return Counter({add(forced,k):v for k,v in classes.items()})
            assert missing==2
            ans=Counter()
            for a,b in combinations(classes,2):ans[add(a,b)]+=classes[a]*classes[b]
            for a,n in classes.items():ans[add(a,a)]+=n*(n-1)//2
            return ans
        removed=choices(W,required,pair)
        added=choices(holes,mandatory_add,common)
        old_even=sum(v.bit_count()%2==0 for v in W);old_r=len(W&N[r]);old_s=len(W&N[s]);count=0
        for (dr,ds,de),nr in removed.items():
            for (ar,ass,ae),na in added.items():
                if 1<=old_r-dr+ar<=2 and 1<=old_s-ds+ass<=2 and old_even-de+ae in (95,96):
                    count+=nr*na
        if count:rows.append(dict(roots=[r,s],source_degrees=[old_r,old_s],forced_deletions=sorted(required),count=count))
    return rows


if __name__=="__main__":
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw);res=[]
    for i in range(25):
        P,sw=project(bank[i]["vertex_sequence"],5);assert len(sw)==1
        rows=pair_rows(P);res.append(dict(source=i,pairs=rows,placements=sum(r["count"] for r in rows)))
    save(Path("crossing-pair-filter.json"),res)
    print(len(res),sum(len(r["pairs"]) for r in res),sum(r["placements"] for r in res),flush=True)
