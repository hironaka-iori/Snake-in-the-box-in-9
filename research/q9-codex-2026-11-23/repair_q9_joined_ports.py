"""Keep the fold crossings and scattered anchors, reselect both eight-dimensional layers."""
import argparse
import json
import random
from pathlib import Path
from retry_q9_six_cube_cycle_cuts import search
from verify_q9_center_avoidance import verify

def attempt(path,target,rng,cap,chord_expected=True):
    chosen=set(path)
    conflicts=[(u,v) for i,u in enumerate(path) for v in path[i+2:] if (u^v).bit_count()==1]
    ports={u for u in path if (u^256) in chosen and all(u not in c for c in conflicts)}
    hot={u for pair in conflicts for u in pair}
    rate=rng.choice([.55,.65,.75,.85])
    fixed=ports|{u for u in path if u not in hot and rng.random()<rate and (not hot or min((u^v).bit_count() for v in hot)>1)}
    assert fixed and (conflicts or not chord_expected)
    st,w=search(fixed,chosen,target,cap,allowed=set(range(512)))
    if w:
        verify(w)
        assert len(w)>target and fixed<=set(w)
    return [len(conflicts),len(ports),len(fixed),rate,st,w]

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('file');ap.add_argument('reps',type=int);ap.add_argument('budget',type=int)
    a=ap.parse_args();rng=random.Random(40243)
    control=list(map(int,Path('q9_forest_ports_control.log').read_text().splitlines()[0].split()[1:]))
    verify(control)
    c=attempt(control,191,rng,25000,False)
    print(json.dumps(['control',*c]),flush=True)
    seeds=[list(map(int,l.split())) for l in Path(a.file).read_text().splitlines()]
    for rep in range(a.reps):
        for i,p in enumerate(seeds):
            r=attempt(p,192,rng,a.budget)
            print(json.dumps([rep,i,*r],separators=(',',':')),flush=True)
            if r[-1]:raise SystemExit
