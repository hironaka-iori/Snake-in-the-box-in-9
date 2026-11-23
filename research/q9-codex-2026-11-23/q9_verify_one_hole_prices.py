"""Replay the punctured donor geometry and all available integer prices without a solver."""
from itertools import combinations, accumulate
from operator import xor
from pathlib import Path
from collections import Counter
import json
import random
from verify_q9_intact98_all_crossings import integer_bound

def parity(v):
    return v.bit_count() & 1
def options(word, index, target):
    arm=list(accumulate([1<<int(c) for c in word],xor,initial=0))
    assert len(set(arm))==len(arm) and all(((x^y).bit_count()==1)==(k==j+1) for k,x in enumerate(arm) for j,y in enumerate(arm[:k]))
    fixed=set(arm)-{arm[index]}
    saturated={x for x in fixed if sum((x^y).bit_count()==1 for y in fixed)>=2}
    spare=sorted(x for x in range(256) if x not in arm and not any((x^y).bit_count()==1 for y in saturated))
    for m in range(1<<len(spare)):
        extra=tuple(x for j,x in enumerate(spare) if m>>j&1)
        low=fixed|set(extra)
        adj={x:{x^1<<d for d in range(8)}&low for x in low}
        if any(len(s)>2 for s in adj.values()):continue
        eligible=sorted(x for x,s in adj.items() if len(s)<2)
        for mask in range(1,1<<len(eligible)):
            ports={v for j,v in enumerate(eligible) if mask>>j&1}
            if any(sum((v^w).bit_count()==1 for w in ports)>1 for v in ports):continue
            reachable=set(ports)
            front=list(ports)
            for v in front:
                new=adj[v]-reachable
                reachable.update(new);front.extend(new)
            if reachable!=low:continue
            degree={v:len(s)+int(v in ports) for v,s in adj.items()}
            if min(degree.values())<1:continue
            bottom=Counter(parity(v) for v,n in degree.items() if n==1)
            for global_even in ([1] if target%2 else [0,2]):
                ends=(global_even-bottom[0],2-global_even-bottom[1])
                if min(ends)<0:continue
                delta=len(low)-2*sum(map(parity,low))-(global_even-1)
                yield (extra,tuple(sorted(ports)),ends,delta),low
def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    blank=dict(axes=axes[:8],scale=1,end_weights=[0,0],balance_weight=0,weights=[])
    closed=[];total=0
    for p in sorted(Path("q9_one_hole_port_prices").glob("*.json")):
        data=json.loads(p.read_text());i=data["index"];h=data["pos"]
        expected=dict(options(bank[i],h,192))
        seen=set();open_branches=0
        for r in data["records"]:
            key=(tuple(r["extra"]),tuple(r["ports"]),tuple(r["upper_ends"]),r["delta"])
            assert key in expected and key not in seen
            seen.add(key);low=expected[key]
            if "empty_table" in r:
                try: integer_bound(blank,low,set(key[1]),key[2],key[3])
                except ValueError as ex: assert str(ex) in ("no possible state for required upper vertex","infeasible affine face")
                else: raise AssertionError("alleged empty table has feasible options")
            else:
                c=r["cert"]
                value=integer_bound(c,low,set(key[1]),key[2],key[3])+len(low)*c["scale"]
                assert value==r["numerator"]
                open_branches+=int(value>=193*c["scale"])
        assert seen==expected.keys()
        total+=len(seen)
        if not open_branches: closed.append([i,h])
    print(json.dumps(dict(checked_branches=total,fully_excluded=closed)))
if __name__=="__main__":main()
