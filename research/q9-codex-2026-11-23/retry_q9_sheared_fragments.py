import sys
from retry_q9_six_cube_sites_cadical import search
from search_q9_sheared_fragments import paircheck
from collections import Counter
cube = set(range(512))
def points(key):
    bits = int(key,16)
    return {x for x in cube if (bits>>x)&1}
budget=int(sys.argv[1]) if len(sys.argv)>1 else 25000
counts=Counter()
for line in sys.stdin:
    t=line.split()
    if t[0]!='UNRESOLVED':continue
    fixed=points(t[1]);host=points(t[2])
    status,w=search(fixed,host,192,budget,allowed=cube)
    counts[status]+=1
    if w:
        assert fixed<=set(w) and len(w)>=193
        paircheck(w)
        print('FOUND',len(w)-1,*w,flush=True);break
    if status=='UNKNOWN':print(line.rstrip(),flush=True)
    if sum(counts.values())%10==0:print('AT',dict(counts),flush=True)
else:print('DONE',dict(counts),flush=True)
