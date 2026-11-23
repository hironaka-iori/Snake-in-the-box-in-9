"""Toggle any single fixed Q9 vertex within one Q8 checkerboard colour."""
from search_q9_checkerboard_walk import half_completion
from search_q9_unordered_projection import project
from verify_q9_center_avoidance import verify
import gzip,json,random,sys
bank=[list(map(int,l.split())) for l in gzip.open('q9_port_followup_public191.txt.gz','rt')]
cases={}
for i,p in enumerate(bank):
    for d in range(9):
        H=project(p,d)
        for c in (0,1):
            A=frozenset(x for x in H if (x%256).bit_count()%2==c)
            cases.setdefault(A,(i,d,c,H))
ordered=list(cases.items());random.Random(92633).shuffle(ordered)
count=int(sys.argv[1]);budget=int(sys.argv[2])
for A,(i,d,c,h) in ordered[:count]:
    for v in range(512):
        if (v%256).bit_count()%2!=c:continue
        st,w=half_completion(A^{v},192,budget,h)
        print(json.dumps([i,d,c,v,st,w],separators=(',',':')),flush=True)
        if w:verify(w);raise SystemExit
