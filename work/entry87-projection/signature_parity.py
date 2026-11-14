"""Independently verify the two parity weights of a closed signature and its toggle law."""
import json
from itertools import combinations
from pathlib import Path
from solve import BANK,BANK_HASH,save,sha256


def signature(s,d):
    t=set(s)
    for x in s:
        for b in range(d):t.symmetric_difference_update((x^(1<<b),))
    return t


def check(s,d):
    t=signature(s,d);edges=sum((x^(1<<b)) in s for x in s for b in range(d))//2
    parts=[sum(v.bit_count()%2==p for v in t) for p in (0,1)]
    assert all((w-len(s)+2*edges)%4==0 for w in parts)
    return t,parts


if __name__=="__main__":
    # Q5 has dimension 1 mod 4. Enumerate all subsets of size at most four
    # and compare their per-parity formula, including cyclic and disconnected sets.
    small=0
    for n in range(5):
        for part in combinations(range(32),n):check(set(part),5);small+=1
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    rows=[]
    for i,r in enumerate(json.loads(raw)):
        s=set(r["vertex_sequence"]);t,counts=check(s,9)
        assert all(n%4==2 for n in counts)
        for v in range(512):
            region={v}|{v^(1<<b) for b in range(9)}
            w=t^region;residue=sum(x.bit_count()%2==0 for x in w)%4
            assert residue==(1 if v in t else 3)
        rows.append(dict(source=i,weights=counts,possible_star_centres=len(t)))
    save(Path("signature-parity.json"),dict(Q5_tests=small,bank=rows))
    print(small,len(rows),sum(r["possible_star_centres"] for r in rows))
