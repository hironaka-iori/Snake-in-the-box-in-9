"""Enumerate lower facets and crossings when exactly one donor point is absent."""
import json
import random
import sys
from itertools import combinations, chain
from pathlib import Path
from q9_rigid_facet_ports import word_path
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound

neighbors = [{v ^ (1 << d) for d in range(8)} for v in range(256)]
def subsets(s):
    return chain.from_iterable(combinations(sorted(s), k) for k in range(len(s) + 1))

def layouts(arm, hole, goal=192):
    fixed = set(arm) - {hole}
    saturated = {v for v in fixed if len(neighbors[v] & fixed) == 2}
    spare = {v for v in range(256) if v not in arm and not neighbors[v] & saturated}
    for extra in subsets(spare):
        low = fixed.union(extra)
        degree = {v: len(neighbors[v] & low) for v in low}
        if max(degree.values()) > 2:
            continue
        components = []
        rem = set(low)
        while rem:
            component = [rem.pop()]
            for v in component:
                more = neighbors[v] & rem
                rem -= more
                component.extend(more)
            components.append(set(component))
        tips = {v for v in low if degree[v] < 2}
        singles = {v for v in tips if degree[v] == 0}
        for subset in subsets(tips - singles):
            ports = singles.union(subset)
            if any(not c & ports for c in components):
                continue
            low_ends = (tips - ports) | singles
            for full_ends in ([(2,0),(0,2)] if goal % 2 == 0 else [(1,1)]):
                ends = [full_ends[h] - sum(v.bit_count() % 2 == h for v in low_ends) for h in range(2)]
                if min(ends) < 0:
                    continue
                if any(len(neighbors[v] & ports) > 1 for v in ports):
                    continue
                delta = sum(1 - 2*(v.bit_count() % 2) for v in low) - (full_ends[0]-full_ends[1])//2
                yield extra, tuple(sorted(ports)), ends, delta, low

def main():
    bank = Path("q8_catalogue_96_98.words").read_text().split()
    plans = []
    for i in (43,44,464,472,576):
        arm = word_path(bank[i])
        for pos,x in enumerate(arm):
            opts = list(layouts(arm,x))
            plans.append((len(opts), pos not in (0,len(arm)-1), i,pos))
    plans.sort()
    if sys.argv[1] == "count":
        from collections import Counter
        print(len(plans),sum(r[0] for r in plans),sorted(Counter(r[0] for r in plans).items()))
        return
    axes=list(combinations(range(8),3))
    random.Random(403215).shuffle(axes)
    dest=Path("q9_one_hole_port_prices")
    dest.mkdir(exist_ok=True)
    for n,_,i,pos in plans:
        out=dest/f"d{i}_h{pos}.json"
        if out.exists(): continue
        arm=word_path(bank[i])
        records=[]
        for extra,ports,ends,delta,low in layouts(arm,arm[pos]):
            result=build(arm,ports,low,ends,delta,axes[:8])
            record=dict(extra=extra,ports=ports,upper_ends=ends,delta=delta)
            if result is None:
                record["empty_table"]=True
            else:
                base,scale,tables,cert=result
                total=base+sum(t[0][2] for _,t in tables)
                assert total==integer_bound(cert,low,set(ports),ends,delta)
                record.update(numerator=total+len(low)*scale,cert=cert)
            records.append(record)
        assert len(records)==n
        tmp=out.with_suffix(".tmp")
        tmp.write_text(json.dumps(dict(index=i,pos=pos,records=records),separators=(",",":")))
        tmp.replace(out)
        unresolved=sum(r.get("numerator",0)>=193*r.get("cert",{}).get("scale",1) for r in records)
        print(i,pos,n,unresolved,flush=True)
if __name__=="__main__": main()
