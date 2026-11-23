"""Release two separated long intervals at the endpoints of a spurious chord.

All vertices outside both intervals must be selected, but their component order
and the length and placement of both replacement pieces are entirely free.
"""
from itertools import product
from pathlib import Path
from retry_q9_six_cube_sites_cadical import search
from repair_q9_time_projection import valid
import argparse, json, random


def bad_edges(p):
    pos={v:i for i,v in enumerate(p)}
    return [(i,j) for i,v in enumerate(p) for d in range(9) if (j:=pos.get(v^(1<<d),-1))>i+1]


def run(p,starts,lengths,target,budget):
    indices=set()
    for start,length in zip(starts,lengths):
        indices.update(range(start,start+length))
    fixed={v for i,v in enumerate(p) if i not in indices}
    st,w=search(fixed,set(p),target,budget,set(range(512)))
    if w is not None:assert valid(w) and fixed<=set(w) and len(w)>target
    return st,w


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('bank');ap.add_argument('limit',type=int);ap.add_argument('budget',type=int)
    ap.add_argument('--control',action='store_true');ap.add_argument('--seed',type=int,default=4809)
    a=ap.parse_args()
    if a.control:
        p=json.loads(Path('q9_explicit_q8_96_plus_94.json').read_text())['vertices']
        print(json.dumps(run(p,[20,112],[36,40],191,a.budget)))
    else:
        rng=random.Random(a.seed)
        bank=[list(map(int,l.split())) for l in Path(a.bank).read_text().splitlines() if l.strip()]
        tasks=[]
        for n,p in enumerate(bank):
            bad=bad_edges(p)
            assert len(p)==193 and len(set(p))==193 and 1<=len(bad)<=2
            for i,j in bad:
                for L,R in ((22,38),(33,33),(30,46),(44,44),(30,55),(50,35),(56,48),(60,60)):
                    for off,off2 in product((0.2,0.5,0.8),repeat=2):
                        s=max(0,min(len(p)-L,i-int(L*off)))
                        t=max(0,min(len(p)-R,j-int(R*off2)))
                        if s+L>=t:continue
                        tasks.append((n,s,t,L,R))
        tasks=sorted(set(tasks));rng.shuffle(tasks)
        seen=set()
        for n,s,t,L,R in tasks:
            p=bank[n];fixed=frozenset(p[:s]+p[s+L:t]+p[t+R:])
            if fixed in seen:continue
            seen.add(fixed)
            st,w=run(p,[s,t],[L,R],192,a.budget)
            print(json.dumps([st,n,s,t,L,R,w],separators=(',',':')),flush=True)
            if w or len(seen)>=a.limit:break
