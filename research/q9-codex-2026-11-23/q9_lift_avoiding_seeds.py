"""Rebuild all three removed coordinates of each new near-record seed."""
import json
from search_q9_cube_fiber_lift import projections, fiber_solve
from search_q9_two_flexible_ends import verify
rows=json.load(open('q9_center_avoidance_verified.json'))['new_witnesses']
seen=set()
for i,r in enumerate(rows):
    p=r['vertices'];verify(p,189)
    steps=[(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
    for base,h in projections(steps,3):
        if base in seen:continue
        seen.add(base)
        st,w=fiber_solve(base,3,192,3000,h)
        if w:verify(w,192)
        print(json.dumps([st,i,base.hex(),w],separators=(',',':')),flush=True)
        if w:raise SystemExit
