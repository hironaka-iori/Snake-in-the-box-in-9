"""Float hidden-coordinate step positions over the best single-cross Q8 joins."""
from search_q9_cube_fiber_lift import projections, fiber_solve, verify
from itertools import combinations
from pathlib import Path
import argparse, json, random

def words(path):
    return [(a^b).bit_length()-1 for a,b in zip(path,path[1:])]

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('d',type=int);ap.add_argument('target',type=int)
    ap.add_argument('count',type=int);ap.add_argument('budget',type=int)
    ap.add_argument('--control',action='store_true');a=ap.parse_args()
    if a.control:
        p=json.loads(Path('q9_explicit_q8_96_plus_94.json').read_text())['vertices']
        bank=[p]
    elif a.target==192:
        bank=[list(map(int,l.split())) for l in Path('q8_single_cross_192_upto2_paths.txt').read_text().splitlines()]
    else:
        bank=[]
        for line in Path(f'q8_complete_single_cross_{a.target}.log').read_text().splitlines():
            t=line.split()
            if t and t[0]=='MIN':bank.append(list(map(int,t[t.index('sample')+1:])))
    tasks=[];seen=set()
    for parent,p in enumerate(bank):
        for axes,(proj,hint) in zip(combinations(range(9),a.d),projections(words(p),a.d)):
            if proj in seen:continue
            seen.add(proj);tasks.append((parent,axes,proj,hint))
    random.Random(3452).shuffle(tasks)
    for parent,axes,proj,hint in tasks[:a.count]:
        status,w=fiber_solve(proj,a.d,a.target,a.budget,hint)
        if w:assert len(w)>a.target and verify(w)
        print(json.dumps([status,parent,axes,len(proj),w],separators=(',',':')),flush=True)
        if w:break
