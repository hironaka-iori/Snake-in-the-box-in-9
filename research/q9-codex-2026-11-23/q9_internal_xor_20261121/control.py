import subprocess,json
from verify import *
w=next(w for w in (ROOT/'q9_reordered_segments_20261120/reference191.words').read_text().split() if all(a!=b for a,b in zip(w,w[1:])) and len(set(p:=vertices(q:=w[:3]+w[4:])))==191 and not quadratic(p))
assert len(p)==191 and len(w)==191 and not quadratic(vertices(w))
seed=canon(q)
out=subprocess.check_output(['/tmp/q9_internal_xor_sweep_20261121','191','3600'],input=seed+'\n',text=True)
emit={(int(t[2]),t[3]) for line in out.splitlines() if (t:=line.split())[0]=='PATH'}
ref=set()
for i in range(1,len(seed)):
    for d in '012345678':
        s=seed[:i]+d+seed[i:];p=vertices(s)
        if len(set(p))!=len(p):continue
        e=len(quadratic(p))
        if e<=4:ref.add((e,canon(s)))
assert emit==ref and (0,canon(w)) in emit
print(json.dumps(dict(seed=seed,reference191=canon(w),deleted_position=3,placements=9*(len(seed)-1),distinct_by_cost=dict(Counter(e for e,s in ref)),all_match=True)))
