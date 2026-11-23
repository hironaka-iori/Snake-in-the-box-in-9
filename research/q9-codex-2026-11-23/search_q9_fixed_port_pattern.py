"""Search fixed cross-layer port sets, allowing both forests to be reshaped."""
import argparse
import json
import random
from pathlib import Path
from retry_q9_six_cube_cycle_cuts import search
from verify_q9_center_avoidance import verify

def run(p,rate,rng,target,budget):
    used=set(p)
    ports={min(x,y) for x,y in zip(p,p[1:]) if x^y==256}
    excess={x for x in used if (x^256) in used and (x&255) not in ports}
    fixed={x for v in ports for x in (v,256+v)}
    for x in used:
        if x not in excess and rng.random()<rate:
            fixed.add(x)
    st,w=search(fixed,used,target,budget,allowed=set(range(512)),cross_ports=ports)
    if w:
        verify(w)
        assert len(w)>target and fixed<=set(w)
        assert set(v for v in w if v<256 and v+256 in w)==ports
    return [rate,len(ports),len(fixed),st,w]

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('source');ap.add_argument('cap',type=int);a=ap.parse_args()
    rng=random.Random(39731)
    p=list(map(int,Path('q9_forest_ports_control.log').read_text().splitlines()[0].split()[1:]))
    c=run(p,.74,rng,191,25000);assert c[-1];print(json.dumps(['control',*c]),flush=True)
    bank=[list(map(int,l.split())) for l in Path(a.source).read_text().splitlines()]
    for rate in (.45,.25,0):
        for i,p in enumerate(bank):
            result=run(p,rate,rng,192,a.cap)
            print(json.dumps([i,*result],separators=(',',':')),flush=True)
            if result[-1]:raise SystemExit
