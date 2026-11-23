"""Reconstruct the full signed half-board after a shear and retry in SAT."""
import json
from search_q9_checkerboard_walk import half_completion
from verify_q9_center_avoidance import verify
bank={}
for l in open('q9_projected_checkerboard_sets.txt'):
    i,c,*verts=map(int,l.split());bank[i]=set(verts)
for l in open('q9_checkerboard_shears.log'):
    fields=l.split()
    if fields[0]!='UNKNOWN':continue
    i,t,m,b=map(int,fields[1:]);assert (t&m).bit_count()%2==0
    A={x^t if ((x&m).bit_count()%2)^b else x for x in bank[i]}
    assert len(A)==len(bank[i])
    st,w=half_completion(A,192,40000,A)
    print(json.dumps([i,t,m,b,st,w],separators=(',',':')),flush=True)
    if w:verify(w);break
