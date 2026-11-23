"""Resolve DFS budgets by replaying their exact signed vertex toggles in the SAT model."""
import argparse,json
from search_q9_checkerboard_walk import half_completion
from verify_q9_center_avoidance import verify
ap=argparse.ArgumentParser();ap.add_argument('log');ap.add_argument('budget',type=int);ap.add_argument('prev',nargs='*');a=ap.parse_args()
base={}
for line in open('q9_projected_checkerboard_sets.txt'):
    i,c,*verts=map(int,line.split());base[i]=frozenset(verts)
done={tuple(r[:-2]) for f in a.prev for r in map(json.loads,open(f)) if r[-2]!='UNKNOWN'}
for line in open(a.log):
    fields=line.split()
    if fields[0]!='UNKNOWN':continue
    k=tuple(map(int,fields[1:]))
    if k in done:continue
    i,*flips=k;A=base[i]^set(flips);st,w=half_completion(A,192,a.budget,A)
    print(json.dumps([*k,st,w],separators=(',',':')),flush=True)
    if w:verify(w);break
