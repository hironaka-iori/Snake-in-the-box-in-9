"""Check distances of all half-full masks and count the first non-extendible seven-faces."""
import json
from collections import Counter, deque
from math import comb
from pathlib import Path

from dense_eight import components
from seven_deletions import generators
from solve import save


def next_sites(forest):
    parts=components(forest,7)
    labels={v:i for i,(edges,part) in enumerate(parts) for v in part}
    adjacent={v:{v^(1<<j) for j in range(7)} for v in range(128)}
    saturated={v for v in forest if len(adjacent[v]&forest)==2}
    extensions=[]
    for v in set(range(128))-forest:
        touch=adjacent[v]&forest
        if len(touch)<=2 and not touch&saturated and len({labels[w] for w in touch})==len(touch):
            extensions.append(v)
    return sorted(extensions)


if __name__=="__main__":
    classes=json.loads(Path("seven-deletion-classes.json").read_bytes())["64"]
    full=set();roots=[];gens=list(generators())
    for row in classes:
        m=sum(1<<v for v in row["forest"]);roots.append(m)
        orbit={m};todo=deque([m])
        while todo:
            x=todo.popleft()
            for _,g in gens:
                w=g(x)
                if w not in orbit:orbit.add(w);todo.append(w)
        assert len(orbit)==row["labelled"] and full.isdisjoint(orbit)
        full.update(orbit)
    dist=[min((m^w).bit_count()//2 for w in full if w!=m) for m in roots]
    assert min(dist)==8 and len(full)==9424
    results={}
    for n in range(60,65):
        counts=Counter()
        witness=None
        for line in Path(f"stream-marked-seven-{n}.txt").read_text().splitlines():
            a,b,c,weight=map(int,line.split());counts[c]+=weight
            if n==61 and witness is None:
                mask=a|(b<<64);sites={v for v in range(128) if mask>>v&1}
                if not next_sites(sites):witness=sorted(sites)
        if n>=62:
            independent=Counter()
            for line in Path(f"marked-seven-{n}.txt").read_text().splitlines():
                a,b,c,weight=map(int,line.split());independent[c]+=weight
            assert independent==counts
        total=sum(counts.values());embedded=len(full)*comb(64,n)
        assert embedded<=total and (embedded==total)==(n>=62)
        results[n]=dict(labelled=total,contained_in_half_full=embedded,outside_half_full=total-embedded,
                        by_components=dict(counts))
        if n==61:
            assert witness is not None
            results[n]["maximal_witness"]=witness
    save(Path("dense-seven-rigidity.json"),dict(full_masks=len(full),exchange_distance_by_full_class=dist,
                                                populations=results))
    print([(n,r["labelled"],r["outside_half_full"]) for n,r in results.items()])
