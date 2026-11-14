"""Check the weight congruence and its exact Q9 modulo-eight refinement on all parity sources."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from solve import BANK,BANK_HASH,sha256,save


def check(S,d):
    counts=Counter(x^(1<<b) for x in S for b in range(d))
    Y={v for v,c in counts.items() if c%2}
    assert (len(Y)-d*len(S))%4==0
    # T2 counts unordered pairs at distance two. Each pair has precisely
    # two common neighbours, so its contribution to the second binomial
    # moment of the number of selected neighbours is exactly two.
    t2=sum((v^w).bit_count()==2 for v,w in combinations(S,2))
    assert sum(c*(c-1)//2 for c in counts.values())==2*t2
    t3=sum(c*(c-1)*(c-2)//6 for c in counts.values())
    assert (len(Y)-d*len(S)+4*t2-4*t3)%8==0
    intersection=S&Y; assert (len(intersection)%2)==0
    return dict(weight=len(S),syndrome=len(Y),distance_two_pairs=t2,triples_at_centres=t3,
                internal_odd_sites=len(intersection))


if __name__=="__main__":
    # Exhaust all subsets of Q4, including non-parity-pure ones.
    for mask in range(1<<16):
        check({v for v in range(16) if mask>>v&1},4)
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    rows=[]
    for i,r in enumerate(json.loads(raw)):
        q=r["vertex_sequence"];S=set(q);a={v for v in S if v.bit_count()%2==0}
        rows.append(dict(source=i,whole=check(S,9),even=check(a,9),odd=check(S-a,9)))
    save(Path("syndrome-mod-four.json"),rows)
    print(len(rows),Counter(r["whole"]["syndrome"]%8 for r in rows),flush=True)
