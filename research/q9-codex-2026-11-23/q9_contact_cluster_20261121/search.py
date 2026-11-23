"""Repair the two ends of an extra chord using graph-local contact clusters."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from retry_q9_six_cube_sites_cadical import search

N = [tuple(v ^ (1 << d) for d in range(9)) for v in range(512)]
CUBE = set(range(512))

def check(p):
    assert all(0 <= v < 512 for v in p) and len(set(p)) == len(p)
    assert all((a ^ b).bit_count() == 1 for a, b in zip(p, p[1:]))
    return [(i,j) for i,a in enumerate(p) for j in range(i+2,len(p)) if (a^p[j]).bit_count()==1]

def release(p, chord, size, rng):
    occupied = set(p)
    pos = {v:i for i,v in enumerate(p)}
    contacts = {v: {pos[w] for w in N[v] if w in occupied} for v in CUBE-occupied}
    released = set(chord)
    while len(released)<size:
        choices = []
        for v, group in contacts.items():
            overlap = len(released & group)
            if overlap and group-released:
                choices.append((v, (overlap**2)/(1+len(group-released))))
        if not choices:
            break
        v, = rng.choices([v for v,_ in choices], [w for _,w in choices], k=1)
        group=contacts[v]
        released.update(group)
        extension=rng.randrange(1,4)
        idx=rng.choice(sorted(group))
        released.update(range(max(0,idx-extension),min(len(p),idx+extension+1)))
    return {v for i,v in enumerate(p) if i not in released}

def run():
    ap=argparse.ArgumentParser()
    ap.add_argument("count",type=int)
    ap.add_argument("budget",type=int)
    ap.add_argument("--seed",type=int,default=448217)
    ap.add_argument("--sizes",type=int,nargs="+",default=[24,40,60,78])
    ap.add_argument("--bank",default="q9_onechord_expanded_800.txt")
    args=ap.parse_args()
    rng=random.Random(args.seed)
    control=json.load(open(HERE.parent/"q9_explicit_q8_96_plus_94.json"))["vertices"]
    assert len(control)==192 and not check(control)
    fixed=release(control,(0,95),30,rng)
    status,w=search(fixed,set(control),191,args.budget,CUBE)
    assert status=="FOUND" and len(w)>=192 and not check(w) and fixed<=set(w)
    print(json.dumps(dict(control_edges=len(w)-1,seed=args.seed)),flush=True)
    bank=[list(map(int,l.split())) for l in open(HERE.parent/args.bank) if l.strip()]
    rng.shuffle(bank)
    stats=Counter()
    for row in range(args.count):
        p=bank[row%len(bank)]
        chord,=check(p)
        assert len(p)==193
        size=args.sizes[row%len(args.sizes)]
        fixed=release(p,chord,size,rng)
        st,w=search(fixed,set(p),192,args.budget,CUBE)
        if w: assert len(w)>=193 and not check(w) and fixed<=set(w)
        stats[st]+=1
        print(json.dumps(dict(row=row,free_old=len(p)-len(fixed),status=st,witness=w),separators=(',',':')),flush=True)
        if w:break
    print(json.dumps(dict(counts=dict(stats))),flush=True)

if __name__=="__main__":
    run()
