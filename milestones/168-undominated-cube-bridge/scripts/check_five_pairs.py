from itertools import combinations
from pathlib import Path
import json,time
start=time.monotonic();pairs=list(combinations(range(9),2));counts=[]
for size in range(6):
    checked=survivors=0
    for edges in combinations(pairs,size):
        checked+=1;deg=[0]*9
        for a,b in edges:deg[a]+=1;deg[b]+=1
        isolated=deg.count(0)
        if isolated>=2:continue
        if isolated==1 and deg.count(1)>=3:continue
        survivors+=1
        isolated_edges=sum(deg[a]==1 and deg[b]==1 for a,b in edges)
        assert isolated==0 and size==5 and sorted(deg)==[1]*8+[2]
        assert isolated_edges==3
    counts.append(dict(edges=size,checked=checked,survivors=survivors))
assert sum(c['survivors'] for c in counts)==3780
result=dict(status='PASS',scope='All simple coordinate graphs on nine labeled vertices with at most five edges; remaining cube interpretation is a written proof',counts=counts,seconds=time.monotonic()-start)
(Path(__file__).resolve().parents[1]/'data/five-pair-classification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
