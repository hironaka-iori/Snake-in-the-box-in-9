"""Within each observed Q5 orientation, add every valid image of a witnessed 14-cycle."""
import gzip,json,sys
from itertools import permutations
from pathlib import Path
from q9_overlapping_port_bound import ROOT, NEIGH
from verify_q9_222_disconnected import components
from q9_port_adversarial_sat import run
from q9_adversarial_port_forests import layouts

def orbit_cuts(cycles,R,F):
    out=set();available=R|F
    for C in cycles[:1]:
        dims=[i for i in range(9) if len({v>>i&1 for v in C})==2]
        assert len(C)==14 and len(dims)==5
        compressed=[sum(((v>>d)&1)<<j for j,d in enumerate(dims)) for v in C]
        masks=set()
        for p in permutations(dims):
            shape=[sum(((v>>j)&1)<<d for j,d in enumerate(p)) for v in compressed]
            for s in range(32):
                t=sum(((s>>j)&1)<<d for j,d in enumerate(dims))
                masks.add(tuple(sorted(v^t for v in shape)))
        for shape in masks:
            for b in range(512):
                if any(b>>d&1 for d in dims):continue
                T=tuple(v|b for v in shape)
                if all(v in available for v in T):out.add(T)
    return sorted(out)

if __name__=="__main__":
    prior={r["case"]:r for r in map(json.loads,gzip.open(ROOT/"q9_port_adversarial_drat.jsonl.gz","rt"))}
    cases=list(layouts());checker=sys.argv[1]
    with gzip.open(ROOT/"q9_port_cycle_orbit_drat.jsonl.gz","wt") as f:
        for i in (7,19,22):
            cuts=lambda R,F:orbit_cuts(prior[i]["cycles"],R,F)
            s,cycles,p=run(cases[i],20000,checker,initial=cuts)
            print(i,s,len(cycles),flush=True)
            f.write(json.dumps(dict(case=i,edges=cases[i],status=s,cycles=cycles,proof=p))+"\n")
